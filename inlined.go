package main

import (
	"debug/dwarf"
	"debug/elf"
	"encoding/binary"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"math"
	"sort"
)

var formatFlag = flag.String("format", "text", "Output format. Valid options are 'json' or 'text'.")
var limitFlag = flag.Uint64("limit", 100, "Number of entries to show. 0 = no limit.")
var sortFlag = flag.String("sort", "total-bytes", "Sorting order. Valid options are 'count', 'instance-bytes', or 'total-bytes'.")

const attrLinkageName dwarf.Attr = 0x6e

type rangeSizeMap map[int64]uint64

// Go's debug/dwarf package doesn't include .debug_ranges parsing support.
func parseDebugRangesFromELF(file *elf.File) (rangeSizeMap, error) {
	log.Print("parsing .debug_ranges...")
	section := file.Section(".debug_ranges")
	if section == nil {
		return nil, nil
	}

	var byteOrder binary.ByteOrder
	switch file.Data {
	case elf.ELFDATA2LSB:
		byteOrder = binary.LittleEndian
	case elf.ELFDATA2MSB:
		byteOrder = binary.BigEndian
	default:
		return nil, fmt.Errorf("%v has an unknown byte order", file)
	}

	var bytesPerAddress uint8
	switch file.Class {
	case elf.ELFCLASS32:
		bytesPerAddress = 4
	case elf.ELFCLASS64:
		bytesPerAddress = 8
	default:
		return nil, fmt.Errorf("%v has unknown class value", file)
	}

	// The .debug_ranges format is pretty simple. A DIE may use DW_AT_ranges to refer to a
	// range in the .debug_ranges section, which represents a range of non-contiguous
	// addresses. Each entry in the range is a either a range list entry, a base address
	// selection entry, or an end of list entry.
	// - A range list entry consists of a beginning address offset and an ending address
	//   offset. The beginning address offset may be 0x0, and the length of the range may be
	//   0, if the beginning and ending address offsets are equal. Range list entries may
	//   not overlap.
	// - A base address selection entry, which consists of the largest representable
	//   address, e.g. 0xffffffff for 32-bit addresses, and an address that defines the base
	//   address of subsequent entries.
	// - An end of list entry is a range list entry that has a beginning and ending address
	//   offset of 0.
	var currentOffset, nextOffset int64
	rangeSizes := make(rangeSizeMap)
	buffer := make([]byte, 2*bytesPerAddress)
	for reader := section.Open(); ; {
		n, err := reader.Read(buffer)
		if n == 0 && err == io.EOF {
			return rangeSizes, nil
		} else if n != len(buffer) {
			return nil, fmt.Errorf("read strange number of bytes: %d", n)
		} else if err != nil {
			return nil, err
		}
		nextOffset += int64(n)
		var begin, end uint64
		switch file.Class {
		case elf.ELFCLASS32:
			begin = uint64(byteOrder.Uint32(buffer))
			end = uint64(byteOrder.Uint32(buffer[4:]))
			if begin == math.MaxUint32 {
				continue
			}
		case elf.ELFCLASS64:
			begin = byteOrder.Uint64(buffer)
			end = byteOrder.Uint64(buffer[8:])
			if begin == math.MaxUint64 {
				continue
			}
		}
		if begin == 0 && end == 0 {
			currentOffset = nextOffset
			continue
		}
		bytes := end - begin
		if bytes < 0 {
			return nil, fmt.Errorf("got invalid range %v", buffer)
		}
		rangeSizes[currentOffset] += bytes
	}
}

type nameMap map[dwarf.Offset]string
type specMap map[dwarf.Offset]dwarf.Offset

// Attempts to extract a function name from the DIE at the provided offset. Unfortunately, since
// it's C++ and DWARF, it's not just a simple matter of getting name attribute and returning it.
func nameForSubprogram(names nameMap, specs specMap, offset dwarf.Offset) (string, error) {
	if specOffset, ok := specs[offset]; ok {
		return nameForSubprogram(names, specs, specOffset)
	}
	if name, ok := names[offset]; ok {
		return name, nil
	}
	return "", fmt.Errorf("could not find name or spec for subprogram 0x%x", offset)
}

func bytesForInlinedSubroutine(rangeSizes rangeSizeMap, entry *dwarf.Entry) (uint64, error) {
	// Per the DWARF spec, a DIE with associated machine code may have:
	// - A DW_AT_low_pc attribute for a snigle address (not handled)
	// - A DW_AT_low_pc and DW_AT_high_pc attribute for a single contiguous range of
	//   addresses, or
	// - A DW_AT_ranges attribute for a non-contiguous range of addresses.

	// TODO(dcheng): This tool should be able to handle either form.
	// The spec notes that DW_AT_high_pc may be either of class address or class constant.
	// In the latter case, DW_AT_high_pc is an offset from DW_AT_low_pc which gives the
	// first instruction past the last instruction associated with the DIE. This code
	// assumes the latter, since that's what Clang emits and it makes the code simpler.
	if bytes, ok := entry.Val(dwarf.AttrHighpc).(int64); ok {
		if bytes < 0 {
			return 0, fmt.Errorf("%v has negative size %d", entry, bytes)
		}
		return uint64(bytes), nil
	}

	rangeOffset, ok := entry.Val(dwarf.AttrRanges).(int64)
	if !ok {
		return 0, fmt.Errorf("%v has no valid high pc or range", entry)
	}
	bytes, ok := rangeSizes[rangeOffset]
	if !ok {
		return 0, fmt.Errorf("couldn't find range entry for %v", entry)
	}
	return bytes, nil
}

type stats struct {
	Count uint64 // Number of times the function was inlined.
	Bytes uint64 // Total bytes inlined for the function.
}
type result struct {
	Name string
	stats
}

func analyze(file *elf.File) ([]*result, error) {
	rangeSizes, err := parseDebugRangesFromELF(file)
	if err != nil {
		return nil, err
	}

	// Strictly speaking, dwarf.Data should have other debug sections too, but in practice,
	// only .debug_info is exposed.
	debugInfo, err := file.DWARF()
	if err != nil {
		return nil, err
	}

	// DIEs may refer to a DIE with a greater offset, so defer name resolution until all DIEs
	// have been read.
	infoReader := debugInfo.Reader()
	names := make(nameMap)
	specs := make(specMap)
	abstractOriginStats := make(map[dwarf.Offset]*stats)
	for i := 0; ; i++ {
		if i%1000000 == 0 {
			log.Printf("read %d DIEs...", i)
		}
		entry, err := infoReader.Next()
		if err != nil {
			return nil, err
		}
		if entry == nil {
			break
		}
		switch entry.Tag {
		case dwarf.TagSubprogram:
			if linkageName, ok := entry.Val(attrLinkageName).(string); ok {
				names[entry.Offset] = linkageName
				continue
			}
			if specOffset, ok := entry.Val(dwarf.AttrSpecification).(dwarf.Offset); ok {
				specs[entry.Offset] = specOffset
				continue
			}
			if name, ok := entry.Val(dwarf.AttrName).(string); ok {
				names[entry.Offset] = name
				continue
			}
		case dwarf.TagInlinedSubroutine:
			abstractOrigin, ok := entry.Val(dwarf.AttrAbstractOrigin).(dwarf.Offset)
			if !ok {
				log.Printf("error: %v missing abstract origin", entry)
				continue
			}
			bytes, err := bytesForInlinedSubroutine(rangeSizes, entry)
			if err != nil {
				log.Printf("error: %v", err)
				continue
			}
			s, ok := abstractOriginStats[abstractOrigin]
			if !ok {
				s = &stats{}
				abstractOriginStats[abstractOrigin] = s
			}
			s.Count++
			s.Bytes += bytes
		}
	}

	log.Printf("resolving names for %d inlined functions", len(abstractOriginStats))
	nameStats := make(map[string]*stats)
	for abstractOrigin, s := range abstractOriginStats {
		name, err := nameForSubprogram(names, specs, abstractOrigin)
		if err != nil {
			log.Printf("error: couldn't extract name for %d: %v", abstractOrigin, err)
		}

		ns, ok := nameStats[name]
		if !ok {
			ns = &stats{}
			nameStats[name] = ns
		}
		ns.Count += s.Count
		ns.Bytes += s.Bytes
	}

	results := make([]*result, 0, len(nameStats))
	for k, v := range nameStats {
		results = append(results, &result{
			Name: k,
			stats: *v,
		})
	}
	return results, nil
}

type by func(r1, r2 *result) bool
type resultSorter struct {
	results []*result
	by by
}

func (by by) Sort(results []*result) {
	rs := &resultSorter{
		results: results,
		by: by,
	}
	sort.Sort(rs)
}

func (s *resultSorter) Len() int {
	return len(s.results)
}

func (s *resultSorter) Swap(i, j int) {
	s.results[i], s.results[j] = s.results[j], s.results[i]
}

func (s *resultSorter) Less(i, j int) bool {
	return s.by(s.results[i], s.results[j])
}

func printSortedResults(results []*result, ordering string, format string, limit uint64) {
	var by by
	switch ordering {
	case "count":
		by = func (r1, r2 *result) bool {
			return r1.Count > r2.Count
		}
	case "instance-bytes":
		by = func (r1, r2 *result) bool {
			return r1.Bytes / r1.Count > r2.Bytes / r2.Count
		}
	case "total-bytes":
		by = func (r1, r2 *result) bool {
			return r1.Bytes > r2.Bytes
		}
	}
	by.Sort(results)

	if limit == 0 || limit > uint64(len(results)) {
		limit = uint64(len(results))
	}
	results = results[:limit]
	switch format {
	case "text":
		fmt.Printf("     Count      Bytes   Name\n")
		fmt.Printf("  --------  ---------   ---------------------------------\n")
		for _, r := range results {
			fmt.Printf("%10d %10d   %s\n", r.Count, r.Bytes, r.Name)
		}
	case "json":
		b, err := json.Marshal(results)
		if err != nil {
			log.Printf("error: JSON result serialization failed: %v", err)
			return
		}
		fmt.Printf("%s\n", b)
	}
}

func main() {
	flag.Parse()
	switch *formatFlag {
	case "json":
	case "text":
	default:
		log.Fatalf("error: invalid option for --format: %s", *formatFlag)
	}
	switch *sortFlag {
	case "count":
	case "instance-bytes":
	case "total-bytes":
	default:
		log.Fatalf("error: invalid option for --sort: %s", *sortFlag)
	}

	for _, f := range flag.Args() {
		log.Printf("analyzing %s...", f)
		file, err := elf.Open(f)
		if err != nil {
			log.Printf("error: couldn't open %s: %v", f, err)
			continue
		}
		defer file.Close()
		results, err := analyze(file)
		if err != nil {
			log.Printf("error: couldn't analyze debug data for %s: %v", f, err)
			continue
		}
		printSortedResults(results, *sortFlag, *formatFlag, *limitFlag)
	}
}

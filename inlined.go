package main

import (
	"debug/dwarf"
	"debug/elf"
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"log"
	"math"
	"os"
	"sort"
)

const attrMIPSLinkageName dwarf.Attr = 0x2007

type rangeSizeMap map[dwarf.Offset]uint64

// Go's debug/dwarf package doesn't include .debug_ranges parsing support.
func parseDebugRangesFromELF(file *elf.File) (rangeSizeMap, error) {
	log.Print("parsing .debug_ranges...")
	sectionReader := file.Section(".debug_ranges").Open()

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
	var currentOffset, pendingOffset dwarf.Offset
	rangeSizes := make(rangeSizeMap)
	buffer := make([]byte, 2*bytesPerAddress)
	for {
		n, err := sectionReader.Read(buffer)
		if n == 0 && err == io.EOF {
			return rangeSizes, nil
		} else if n != len(buffer) {
			return nil, fmt.Errorf("read strange number of bytes: %d", n)
		} else if err != nil {
			return nil, err
		}
		pendingOffset += dwarf.Offset(n)
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
			currentOffset = pendingOffset
			continue
		}
		bytes := end - begin
		if bytes < 0 {
			return nil, fmt.Errorf("got invalid range %v", buffer)
		}
		rangeSizes[currentOffset] += bytes
	}
}

type subprogramEntry struct {
	name string
	linkageName string
	hasSpecOffset bool
	specOffset dwarf.Offset
}
type subprogramMap map[dwarf.Offset]*subprogramEntry

// Attempts to extract a function name from the DIE at the provided offset. Unfortunately, since
// it's C++ and DWARF, it's not just a simple matter of getting name attribute and returning it.
func nameForEntry(subprograms subprogramMap, offset dwarf.Offset) (string, error) {
	subprogram, ok := subprograms[offset]
	if !ok {
		return "", errors.New("couldn't find subprogram")
	}

	if subprogram.linkageName != "" {
		return subprogram.linkageName, nil
	}

	if subprogram.hasSpecOffset {
		return nameForEntry(subprograms, subprogram.specOffset)
	}

	if subprogram.name != "" {
		return subprogram.name, nil
	}

	return "", fmt.Errorf("subprogram 0x%x has no name, linkage name, or spec", offset)
}

func bytesForEntry(rangeSizes rangeSizeMap, entry *dwarf.Entry) (uint64, error) {
	// Per the DWARF spec, a DIE with associated machine code may have:
	// - A DW_AT_low_pc attribute for a snigle address (not handled)
	// - A DW_AT_low_pc and DW_AT_high_pc attribute for a single contiguous range of
	//   addresses, or
	// - A DW_AT_ranges attribute for a non-contiguous range of addresses.

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

	rangeOffset, ok := entry.Val(dwarf.AttrRanges).(dwarf.Offset)
	if !ok {
		return 0, fmt.Errorf("%v has no valid high pc or range", entry)
	}
	bytes, ok := rangeSizes[rangeOffset]
	if !ok {
		return 0, fmt.Errorf("couldn't find range entry for %v", entry)
	}
	return bytes, nil
}

type inlineStats struct {
	count uint64 // Number of times the function was inlined.
	bytes uint64 // Total bytes inlined for the function.
}

func analyze(file *elf.File) (map[string]*inlineStats, error) {
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

	// DIEs may refer to a DIE with a greater offset, so collect all interesting DIEs first.
	infoReader := debugInfo.Reader()
	subprograms := make(subprogramMap)
	inlinedSubroutines := make([]*dwarf.Entry, 0, 1024)
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
			subprogram := &subprogramEntry{}
			if name, ok := entry.Val(attrMIPSLinkageName).(string); ok {
				subprogram.linkageName = name
			}
			if specOffset, ok := entry.Val(dwarf.AttrSpecification).(dwarf.Offset); ok {
				subprogram.hasSpecOffset = true
				subprogram.specOffset = specOffset
			}
			if name, ok := entry.Val(dwarf.AttrName).(string); ok {
				subprogram.name = name
			}
			subprograms[entry.Offset] = subprogram
		case dwarf.TagInlinedSubroutine:
			inlinedSubroutines = append(inlinedSubroutines, entry)
		}
	}

	log.Printf("got %d inlined subroutines", len(inlinedSubroutines))
	results := make(map[string]*inlineStats)
	for _, entry := range inlinedSubroutines {
		subprogramOffset, ok := entry.Val(dwarf.AttrAbstractOrigin).(dwarf.Offset)
		if !ok {
			log.Printf("error: %v missing abstract origin", entry)
			continue
		}
		name, err := nameForEntry(subprograms, subprogramOffset)
		if err != nil {
			log.Printf("error: couldn't extract name for %v: %v", entry, err)
		}

		bytes, err := bytesForEntry(rangeSizes, entry)

		info, ok := results[name]
		if !ok {
			info = &inlineStats{}
			results[name] = info
		}
		info.count++
		info.bytes += uint64(bytes)
	}
	return results, nil
}

type resultSorter struct {
	// TOOO(dcheng): Bad names are bad.
	keys    []string
	results map[string]*inlineStats
}

func (s *resultSorter) Len() int {
	return len(s.keys)
}

func (s *resultSorter) Swap(i, j int) {
	s.keys[i], s.keys[j] = s.keys[j], s.keys[i]
}

func (s *resultSorter) Less(i, j int) bool {
	return s.results[s.keys[i]].bytes > s.results[s.keys[j]].bytes
}

func sortAndPrintTop100(results map[string]*inlineStats) {
	keys := make([]string, 0, len(results))
	for k := range results {
		keys = append(keys, k)
	}
	sort.Sort(&resultSorter{keys, results})
	fmt.Printf("     Count      Bytes   Name\n")
	fmt.Printf("  --------  ---------   ---------------------------------\n")
	for i, k := range keys {
		if i > 100 {
			break
		}
		fmt.Printf("%10d %10d   %s\n", results[k].count, results[k].bytes, k)
	}
}

func main() {
	for _, f := range os.Args[1:] {
		log.Printf("analyzing %s...", f)
		file, err := elf.Open(f)
		if err != nil {
			log.Printf("error: couldn't open %s: %v", f, err)
			continue
		}
		results, err := analyze(file)
		if err != nil {
			log.Printf("error: couldn't analyze debug data for %s: %v", f, err)
			continue
		}
		sortAndPrintTop100(results)
	}
}

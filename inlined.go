package main

import (
	"debug/dwarf"
	"debug/elf"
	"errors"
	"fmt"
	"log"
	"os"
	"sort"
)

const attrMIPSLinkageName dwarf.Attr = 0x2007

type costInfo struct {
	count uint64 // Number of times the function was inlined.
	bytes uint64 // Total bytes inlined for the function.
}

type subprogramMap map[dwarf.Offset]*dwarf.Entry

// Attempts to extract a function name from the DIE at the provided offset. Unfortunately, since
// it's C++ and DWARF, it's not just a simple matter of getting name attribute and returning it.
func nameForEntry(subprograms subprogramMap, offset dwarf.Offset) (string, error) {
	subprogram, ok := subprograms[offset]
	if !ok {
		return "", errors.New("couldn't find subprogram")
	}

	// TODO(dcheng): Ideally, demangle this name.
	if name, ok := subprogram.Val(attrMIPSLinkageName).(string); ok {
		return name, nil
	}

	// Some DIEs chain to another DIE with the specification attribute.
	// TODO(dcheng): Document when this happens.
	if specOffset, ok := subprogram.Val(dwarf.AttrSpecification).(dwarf.Offset); ok {
		return nameForEntry(subprograms, specOffset)
	}

	// Otherwise, fall back to the name attribute. This is probably a plain C function.
	if name, ok := subprogram.Val(dwarf.AttrName).(string); ok {
		return name, nil
	}

	return "", fmt.Errorf("%v missing name, linkage name, and spec", subprogram)
}

func analyze(data *dwarf.Data) (map[string]*costInfo, error) {
	// DIEs may refer to a DIE with a greater offset, so collect all interesting DIEs first.
	reader := data.Reader()
	subprograms := make(subprogramMap)
	inlinedSubroutines := make([]*dwarf.Entry, 0, 1024)
	for i := 0; ; i++ {
		if i % 1000000 == 0 {
			log.Printf("read %d DIEs...", i)
		}
		entry, err := reader.Next()
		if err != nil {
			return nil, err
		}
		if entry == nil {
			break
		}
		switch entry.Tag {
		case dwarf.TagSubprogram:
			subprograms[entry.Offset] = entry
		case dwarf.TagInlinedSubroutine:
			inlinedSubroutines = append(inlinedSubroutines, entry)
		}
	}

	log.Printf("got %d inlined subroutines", len(inlinedSubroutines))
	results := make(map[string]*costInfo)
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

		// Despite the name, this is relative to Lowpc, so it's actually a byte count.
		bytes, ok := entry.Val(dwarf.AttrHighpc).(int64)
		if !ok {
			// TODO(dcheng): Handle AttrRanges.
			continue
			log.Printf("error: couldn't extract AttrHighpc for %v", entry)
		}
		if bytes < 0 {
			log.Printf("error: %v has a negative AttrHighpc", entry)
			continue
		}

		info, ok := results[name]
		if !ok {
			info = &costInfo{}
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
	results map[string]*costInfo
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

func sortAndPrintTop100(results map[string]*costInfo) {
	keys := make([]string, 0, len(results))
	for k := range results {
		keys = append(keys, k)
	}
	sort.Sort(&resultSorter{keys, results})
	for i, k := range keys {
		if i > 100 {
			break
		}
		log.Printf("Function %s was inlined %d times and used %d bytes",
			k, results[k].count, results[k].bytes)
	}
}

func main() {
	for _, f := range os.Args[1:] {
		log.Printf("Analyzing %s...\n", f)
		elf, err := elf.Open(f)
		if err != nil {
			log.Printf("error: couldn't open %s: %v", f, err)
			continue
		}
		debugData, err := elf.DWARF()
		if err != nil {
			log.Printf("error: couldn't load debug data for %s: %v", f, err)
			continue
		}
		results, err := analyze(debugData)
		if err != nil {
			log.Printf("error: couldn't analyze debug data for %s: %v", f, err)
			continue
		}
		sortAndPrintTop100(results)
	}
}

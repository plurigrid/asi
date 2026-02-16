// Package sims_parser provides DBPF (Database Packed File) parsing for The Sims games.
// Supports Sims 2, Sims 3, and Sims 4 package formats.
package sims_parser

import (
	"bytes"
	"encoding/binary"
	"fmt"
	"io"
)

// DBPFVersion represents the DBPF format version
type DBPFVersion uint32

const (
	DBPFVersion1_0 DBPFVersion = 1
	DBPFVersion1_1 DBPFVersion = 2
	DBPFVersion2_0 DBPFVersion = 3 // Sims 3 & 4
)

// DBPFHeader represents the DBPF file header
type DBPFHeader struct {
	Magic           [4]byte // "DBPF"
	MajorVersion    uint32
	MinorVersion    uint32
	Reserved        [16]byte
	FileSize        uint32
	IndexCount      uint32
	IndexOffset     uint32
	IndexSize       uint32
	HoleIndexCount  uint32
	HoleIndexOffset uint32
	HoleIndexSize   uint32
	CreatedDate     uint32
	ModifiedDate    uint32
	IndexMinor      uint32
}

// ResourceEntry represents a single resource in the DBPF
type ResourceEntry struct {
	ResourceType uint32
	ResourceGroup uint32
	ResourceID   uint64
	Offset       uint32
	Compressed   uint32 // Size if compressed, 0xFFFFFFFF if uncompressed
	RawSize      uint32
	TypeID       uint32 // Sims 4 only
}

// DBPFPackage represents a complete DBPF package file
type DBPFPackage struct {
	Header    DBPFHeader
	Resources []*ResourceEntry
	Content   []byte
}

// NewDBPFPackage parses a DBPF file from a reader
func NewDBPFPackage(r io.Reader) (*DBPFPackage, error) {
	data, err := io.ReadAll(r)
	if err != nil {
		return nil, fmt.Errorf("failed to read file: %w", err)
	}

	if len(data) < 96 {
		return nil, fmt.Errorf("file too small for DBPF header")
	}

	pkg := &DBPFPackage{Content: data}

	// Parse header
	buf := bytes.NewReader(data[:96])
	if err := binary.Read(buf, binary.LittleEndian, &pkg.Header); err != nil {
		return nil, fmt.Errorf("failed to parse DBPF header: %w", err)
	}

	// Verify magic
	if string(pkg.Header.Magic[:]) != "DBPF" {
		return nil, fmt.Errorf("invalid DBPF magic bytes: %v", pkg.Header.Magic)
	}

	// Parse index entries
	if pkg.Header.IndexCount > 0 && pkg.Header.IndexOffset > 0 {
		if err := pkg.parseIndex(data); err != nil {
			return nil, err
		}
	}

	return pkg, nil
}

func (p *DBPFPackage) parseIndex(data []byte) error {
	offset := p.Header.IndexOffset
	entrySize := uint32(24) // Standard for Sims 2/3

	// Check if Sims 4 format (7.1 index with type IDs)
	if p.Header.IndexMinor == 1 && p.Header.MajorVersion >= 1 {
		entrySize = 32 // Includes TypeID field
	}

	for i := uint32(0); i < p.Header.IndexCount; i++ {
		if offset+entrySize > uint32(len(data)) {
			return fmt.Errorf("index entry extends beyond file")
		}

		entry := &ResourceEntry{}
		buf := bytes.NewReader(data[offset : offset+entrySize])

		// Read base fields (all versions)
		var typeGroup uint32
		binary.Read(buf, binary.LittleEndian, &entry.ResourceType)
		binary.Read(buf, binary.LittleEndian, &typeGroup)
		binary.Read(buf, binary.LittleEndian, &entry.ResourceGroup)
		
		// Read resource ID (8 bytes for Sims 3/4)
		var id32 uint32
		binary.Read(buf, binary.LittleEndian, &id32)
		binary.Read(buf, binary.LittleEndian, &entry.ResourceID)
		entry.ResourceID = (entry.ResourceID << 32) | uint64(id32)

		binary.Read(buf, binary.LittleEndian, &entry.Offset)
		binary.Read(buf, binary.LittleEndian, &entry.Compressed)
		binary.Read(buf, binary.LittleEndian, &entry.RawSize)

		// Sims 4 has TypeID
		if entrySize == 32 {
			binary.Read(buf, binary.LittleEndian, &entry.TypeID)
		}

		p.Resources = append(p.Resources, entry)
		offset += entrySize
	}

	return nil
}

// GetResource retrieves a resource by type, group, and ID
func (p *DBPFPackage) GetResource(resType, group, id uint32) ([]byte, error) {
	for _, entry := range p.Resources {
		if entry.ResourceType == resType && entry.ResourceGroup == group {
			if uint32(entry.ResourceID) == id {
				return p.extractResourceData(entry)
			}
		}
	}
	return nil, fmt.Errorf("resource not found: type=%08x group=%08x id=%08x", resType, group, id)
}

func (p *DBPFPackage) extractResourceData(entry *ResourceEntry) ([]byte, error) {
	if entry.Offset > uint32(len(p.Content)) {
		return nil, fmt.Errorf("resource offset beyond file")
	}

	// Check if compressed (Compressed != 0xFFFFFFFF)
	if entry.Compressed != 0xFFFFFFFF && entry.Compressed > 0 {
		// QFS/RefPack compression (Sims 2/3)
		compressedData := p.Content[entry.Offset : entry.Offset+entry.Compressed]
		return decompressQFS(compressedData, entry.RawSize)
	}

	// Uncompressed or check for ZLIB (Sims 4)
	if entry.RawSize > 0 {
		return p.Content[entry.Offset : entry.Offset+entry.RawSize], nil
	}

	return nil, fmt.Errorf("invalid resource size")
}

// GameVersion returns detected Sims game version based on format
func (p *DBPFPackage) GameVersion() string {
	switch {
	case p.Header.MajorVersion == 1 && p.Header.MinorVersion <= 1:
		return "Sims 2"
	case p.Header.MajorVersion == 2 && p.Header.IndexMinor == 0:
		return "Sims 3"
	case p.Header.MajorVersion == 2 && p.Header.IndexMinor == 1:
		return "Sims 4"
	default:
		return "Unknown"
	}
}

// ListResources returns a summary of all resources in the package
func (p *DBPFPackage) ListResources() []ResourceSummary {
	summaries := make([]ResourceSummary, len(p.Resources))
	for i, entry := range p.Resources {
		summaries[i] = ResourceSummary{
			ResourceType:  entry.ResourceType,
			ResourceGroup: entry.ResourceGroup,
			ResourceID:    entry.ResourceID,
			Size:          entry.RawSize,
			IsCompressed:  entry.Compressed != 0xFFFFFFFF,
		}
	}
	return summaries
}

// ResourceSummary provides a summary view of a resource
type ResourceSummary struct {
	ResourceType  uint32
	ResourceGroup uint32
	ResourceID    uint64
	Size          uint32
	IsCompressed  bool
}

// CompressedSizeValue returns the compressed size for an entry
func (e *ResourceEntry) CompressedSizeValue() uint32 {
	if e.Compressed == 0xFFFFFFFF {
		return e.RawSize
	}
	return e.Compressed
}

// decompressQFS decompresses QFS/RefPack compressed data
func decompressQFS(compressed []byte, expectedSize uint32) ([]byte, error) {
	// Placeholder: QFS decompression would go here
	// For now, return compressed as-is (would need actual QFS implementation)
	if uint32(len(compressed)) == expectedSize {
		return compressed, nil
	}
	return nil, fmt.Errorf("QFS decompression not yet implemented")
}

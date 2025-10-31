//go:build !dev

package plot

import (
	"embed"
	"io"
	"io/fs"
	"net/http"
	"os"
)

//go:embed assets/*
var assetsFS embed.FS

// Assets contains assets required to render the Plot.
var Assets http.FileSystem = &embedFS{assetsFS}

type embedFS struct {
	fs embed.FS
}

func (e *embedFS) Open(name string) (http.File, error) {
	f, err := e.fs.Open("assets/" + name)
	if err != nil {
		return nil, err
	}

	stat, err := f.Stat()
	if err != nil {
		return nil, err
	}

	if stat.IsDir() {
		return &embedFile{File: f}, nil
	}

	// For regular files, read all content to support Seek
	data, err := io.ReadAll(f)
	if err != nil {
		return nil, err
	}
	f.Close()

	return &embedFileSeeker{
		File:   f,
		data:   data,
		reader: io.NewSectionReader(&bytesReaderAt{data}, 0, int64(len(data))),
	}, nil
}

type embedFile struct {
	fs.File
}

func (f *embedFile) Readdir(count int) ([]os.FileInfo, error) {
	return nil, nil
}

func (f *embedFile) Seek(offset int64, whence int) (int64, error) {
	return 0, nil
}

type embedFileSeeker struct {
	fs.File
	data   []byte
	reader *io.SectionReader
}

func (f *embedFileSeeker) Read(p []byte) (int, error) {
	return f.reader.Read(p)
}

func (f *embedFileSeeker) Seek(offset int64, whence int) (int64, error) {
	return f.reader.Seek(offset, whence)
}

func (f *embedFileSeeker) Readdir(count int) ([]os.FileInfo, error) {
	return nil, nil
}

type bytesReaderAt struct {
	data []byte
}

func (r *bytesReaderAt) ReadAt(p []byte, off int64) (n int, err error) {
	if off < 0 || off >= int64(len(r.data)) {
		return 0, io.EOF
	}
	n = copy(p, r.data[off:])
	if n < len(p) {
		err = io.EOF
	}
	return
}

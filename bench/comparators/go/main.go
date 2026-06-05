// Go DEFLATE comparator for the lean-zip Track D dashboard.
//
// Reads a raw payload file, compresses+decompresses it with the pure-Go
// standard-library `compress/flate`, and prints one JSON object:
//
//	{"out_size":N,"compress_mbps":X,"decompress_mbps":Y}
//
// Timing mirrors ZipBenchReport.lean exactly: median-of-5 reps, each rep timing
// `itersFor(size)` iterations, throughput measured against the *uncompressed*
// byte count. Usage: bench-go <payload.bin> <level>
package main

import (
	"bytes"
	"compress/flate"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"sort"
	"strconv"
	"time"
)

var sink int // accumulates work so the compiler can't elide the timed calls

func itersFor(size int) int {
	switch {
	case size <= 16384:
		return 50
	case size <= 262144:
		return 10
	case size <= 1048576:
		return 3
	default:
		return 1
	}
}

func deflate(data []byte, level int) []byte {
	var buf bytes.Buffer
	w, err := flate.NewWriter(&buf, level)
	if err != nil {
		panic(err)
	}
	if _, err := w.Write(data); err != nil {
		panic(err)
	}
	if err := w.Close(); err != nil {
		panic(err)
	}
	return buf.Bytes()
}

func inflate(comp []byte) []byte {
	r := flate.NewReader(bytes.NewReader(comp))
	out, err := io.ReadAll(r)
	if err != nil {
		panic(err)
	}
	r.Close()
	return out
}

func median(xs []int64) int64 {
	sort.Slice(xs, func(i, j int) bool { return xs[i] < xs[j] })
	return xs[len(xs)/2]
}

// medianNsPerOp times `iters` calls to `op`, repeated 5×, returning the median
// per-op nanoseconds.
func medianNsPerOp(iters int, op func() int) int64 {
	reps := make([]int64, 0, 5)
	for r := 0; r < 5; r++ {
		t0 := time.Now()
		for i := 0; i < iters; i++ {
			sink += op()
		}
		ns := time.Since(t0).Nanoseconds() / int64(max(iters, 1))
		reps = append(reps, ns)
	}
	return median(reps)
}

func mbps(size int, nsPerOp int64) float64 {
	if nsPerOp == 0 {
		return 0
	}
	return (float64(size) / (1024.0 * 1024.0)) / (float64(nsPerOp) / 1e9)
}

func round2(f float64) float64 {
	return float64(int64(f*100.0+0.5)) / 100.0
}

func main() {
	if len(os.Args) != 3 {
		fmt.Fprintln(os.Stderr, "usage: bench-go <payload.bin> <level>")
		os.Exit(2)
	}
	data, err := os.ReadFile(os.Args[1])
	if err != nil {
		panic(err)
	}
	level, err := strconv.Atoi(os.Args[2])
	if err != nil {
		panic(err)
	}
	size := len(data)
	iters := itersFor(size)

	comp := deflate(data, level)
	if !bytes.Equal(inflate(comp), data) {
		panic("roundtrip mismatch: inflate(deflate(data)) != data")
	}
	cNs := medianNsPerOp(iters, func() int { return len(deflate(data, level)) })
	dNs := medianNsPerOp(iters, func() int { return len(inflate(comp)) })

	if sink == 0 {
		fmt.Fprintln(os.Stderr, "unreachable")
	}
	out, _ := json.Marshal(map[string]any{
		"out_size":        len(comp),
		"compress_mbps":   round2(mbps(size, cNs)),
		"decompress_mbps": round2(mbps(size, dNs)),
	})
	fmt.Println(string(out))
}

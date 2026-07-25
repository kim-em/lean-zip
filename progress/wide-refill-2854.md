# Word-at-a-time decoder refill (#2854)

## Benchmark-first result

The implementation replaces `goCurU`'s recursive byte refill with one unaligned
64-bit load and an exact byte-count update:

```text
k      := (64 - cnt) >> 3
bitBuf |= ugetUInt64LE(data, pos) << cnt
pos    += k
cnt    := 64 - ((64 - cnt) & 7)
```

The update runs only behind an eight-byte input margin. The final input tail
continues through the existing byte-at-a-time refill. Unlike the raw
libdeflate-shaped spike, this form advances by exactly the number of bytes that
the old loop would consume, which makes the old and new decoder states directly
equivalent after speculative high bits are trimmed.

Measurements are same-worktree `perf stat -r 5`, 40 decode repetitions per
sample, using LTO-built binaries and Silesia level-6 raw-DEFLATE payloads. Lower
is better.

| corpus | baseline cycles | exact-wide cycles | delta | baseline instructions | exact-wide instructions | delta |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| x-ray | 7,971,160,745 | 7,556,385,788 | -5.20% | 33,885,213,053 | 34,746,232,504 | +2.54% |
| dickens | 6,295,589,041 | 6,071,650,189 | -3.56% | 24,050,736,857 | 24,250,819,894 | +0.83% |
| nci | 7,074,985,342 | 6,778,917,179 | -4.18% | 25,417,946,741 | 25,774,013,713 | +1.40% |

All timed binaries first decoded each payload and checked it byte-for-byte
against the reference decoder. The result is consistently cycle-positive even
though instruction counts rise: the benefit is the shorter dependent refill
chain, not less total work.

The cycle-count relative standard deviations reported by `perf` were 0.14% /
0.06% (baseline / exact-wide) for x-ray, 0.14% / 0.14% for dickens, and 0.25% /
0.16% for nci. Mean application-reported throughput across the five runs was:

| corpus | baseline MB/s | exact-wide MB/s | delta |
| --- | ---: | ---: | ---: |
| x-ray | 201.866 | 213.180 | +5.60% |
| dickens | 309.222 | 320.314 | +3.59% |
| nci | 932.877 | 977.273 | +4.76% |

CPU frequency was not pinned; baseline and candidate were run back-to-back on
the same host. The low `perf` variation and positive result on every corpus are
the primary signal; throughput is included as a secondary wall-clock view.

## Rejected spike

The initial raw libdeflate update used `(63 - cnt) >> 3` and `cnt |= 56`. It was
faster (-8.4%, -7.0%, and -3.9% cycles on x-ray, dickens, and nci), but it does
not preserve the byte refiller's exact `(pos, cnt)` state. In particular, when
`cnt` is byte-aligned it may stop at exactly 56 counted bits without advancing
the eighth byte, whereas the old `cnt ≤ 56` refiller consumes that byte and
stops at 64. The absolute stream bit position still agrees, but landing that
shape would require replacing the production proof's full returned-tuple
equality with a representation-equivalence relation through EOB cursor
reconstruction and every block-loop caller. That larger proof/API change is
separable from this input-margin optimization and can be re-probed alongside
the multi-symbol work in #2856. The implementation here therefore uses the
exact update above. An eager wide top-up (the #2630 shape) and a dynamically
masked load were also neutral or slower controls.

## Correctness shape

The wide loop carries genuine future stream bits above its logical `cnt`; they
are not arbitrary garbage. Input- and output-margin exits trim those
speculative bits before returning to the byte refiller or `goCur`. The proof
tracks the counted low bits, proves the 64-bit load extends them with the same
bytes as repeated `refill`, and shows that literal, end-of-block, length, and
distance consumption preserve the relation. The generated Huffman tables are
also connected to the proof's maximum-code-length premise, and the proof module
is imported by the default `Zip` build.

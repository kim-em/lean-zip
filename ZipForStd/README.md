# ZipForStd

Lemmas and definitions for Lean's standard library types that are missing
upstream but needed by lean-zip proofs.

## Organization

Files are named after the namespace they extend, e.g.:

    ZipForStd/ByteArray.lean   — lemmas in the `ByteArray` namespace
    ZipForStd/Array.lean       — lemmas in the `Array` namespace

Put theorems in the appropriate namespace so they look like they belong
to the standard library. This makes upstreaming straightforward: the
lemma names and namespaces are already correct.

## Upstreaming

Anything in this directory is a candidate for upstreaming to Lean's
standard library or Batteries. When a lemma here gets accepted upstream,
remove it and bump the toolchain.

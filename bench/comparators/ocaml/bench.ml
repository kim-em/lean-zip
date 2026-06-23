(* OCaml DEFLATE comparator for the lean-zip Track D dashboard.

   Uses the pure-OCaml `decompress` library (mirage/decompress), specifically
   its RFC1951 raw-DEFLATE codec `De` (sublibrary decompress.de). We drive the
   library's `De.Higher` streaming helpers over the whole payload in one go;
   `Higher.compress`/`uncompress` are documented as the equivalent of
   `Zlib.{compress,uncompress} ~header:false`, i.e. raw DEFLATE with no
   zlib/gzip wrapper.

   Honours the shared comparator contract:

     bench <payload.bin> <level>  ->  stdout JSON
     {"out_size":N,"compress_mbps":X,"decompress_mbps":Y}

   Timing mirrors ZipBenchReport.lean / the Go and JS comparators: median-of-5
   reps, itersFor(size) iters per rep, throughput measured against the
   *uncompressed* byte count. Self-verifies its roundtrip before timing. *)

type bigstring =
  (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

let sink = ref 0 (* accumulate work so it isn't optimized away *)

let iters_for size =
  if size <= 16384 then 50
  else if size <= 262144 then 10
  else if size <= 1048576 then 3
  else 1

(* Whole-file raw bytes as an OCaml string. *)
let read_file path : string =
  let ic = open_in_bin path in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic;
  s

let io = De.io_buffer_size

(* blit [len] bytes of [src] starting at [off] into bigstring [dst]. *)
let blit_string_to_bigstring src ~src_off (dst : bigstring) ~len =
  for i = 0 to len - 1 do
    Bigarray.Array1.unsafe_set dst i (String.unsafe_get src (src_off + i))
  done

(* append [len] bytes of bigstring [src] to Buffer [b]. *)
let buffer_add_bigstring b (src : bigstring) ~len =
  for i = 0 to len - 1 do
    Buffer.add_char b (Bigarray.Array1.unsafe_get src i)
  done

(* Raw DEFLATE of [str] at [level].

   `De.Higher.compress` hardcodes the default LZ77 level, so we inline its
   compress loop (verbatim structure from decompress's de.ml) and thread the
   requested [~level] into `Lz77.state`. The encoder emits Dynamic blocks for
   the body and a final Fixed last-block, exactly as `Higher.compress` does. *)
let deflate (str : string) (level : int) : string =
  let module Q = De.Queue in
  let module Def = De.Def in
  let module Lz77 = De.Lz77 in
  let i = De.bigstring_create io in
  let o = De.bigstring_create io in
  let w = Lz77.make_window ~bits:15 in
  let q = Q.create 0x1000 in
  let r = Buffer.create 0x1000 in
  let p = ref 0 in
  let refill buf =
    let len = min (String.length str - !p) io in
    blit_string_to_bigstring str ~src_off:!p buf ~len;
    p := !p + len;
    len
  in
  let flush buf len = buffer_add_bigstring r buf ~len in
  let state = Lz77.state ~level `Manual ~w ~q in
  let encoder = Def.encoder `Manual ~q in
  let rec compress () =
    match Lz77.compress state with
    | `Await ->
      let len = refill i in
      Lz77.src state i 0 len; compress ()
    | `Flush ->
      let literals = Lz77.literals state in
      let distances = Lz77.distances state in
      let kind = Def.Dynamic (Def.dynamic_of_frequencies ~literals ~distances) in
      encode (Def.encode encoder (`Block {Def.kind; last= false}))
    | `End ->
      pending (Def.encode encoder (`Block {Def.kind= Def.Fixed; last= true}))
  and encode = function
    | `Partial ->
      let len = De.bigstring_length o - Def.dst_rem encoder in
      flush o len;
      Def.dst encoder o 0 (De.bigstring_length o);
      encode (Def.encode encoder `Await)
    | `Ok -> compress ()
    | `Block ->
      let literals = Lz77.literals state in
      let distances = Lz77.distances state in
      let kind = Def.Dynamic (Def.dynamic_of_frequencies ~literals ~distances) in
      encode (Def.encode encoder (`Block {Def.kind; last= false}))
  and pending = function
    | `Block -> assert false
    | `Partial ->
      let len = De.bigstring_length o - Def.dst_rem encoder in
      flush o len;
      Def.dst encoder o 0 (De.bigstring_length o);
      pending (Def.encode encoder `Await)
    | `Ok -> ()
  in
  Q.reset q;
  Def.dst encoder o 0 (De.bigstring_length o);
  compress ();
  Buffer.contents r

(* Raw INFLATE of [str], via De.Higher.uncompress. *)
let inflate (str : string) : string =
  let i = De.bigstring_create io in
  let o = De.bigstring_create io in
  let w = De.make_window ~bits:15 in
  let r = Buffer.create 0x1000 in
  let p = ref 0 in
  let refill buf =
    let len = min (String.length str - !p) io in
    blit_string_to_bigstring str ~src_off:!p buf ~len;
    p := !p + len;
    len
  in
  let flush buf len = buffer_add_bigstring r buf ~len in
  match De.Higher.uncompress ~w ~refill ~flush i o with
  | Ok () -> Buffer.contents r
  | Error (`Msg m) ->
    Printf.eprintf "inflate error: %s\n%!" m;
    exit 1

(* Wall-clock nanoseconds via Unix.gettimeofday (seconds, float). *)
let now_ns () = Unix.gettimeofday () *. 1e9

let median (xs : float array) : float =
  Array.sort compare xs;
  xs.(Array.length xs / 2)

(* Time [iters] calls to [op], repeated 5x, returning median per-op ns. *)
let median_ns_per_op iters (op : unit -> int) : float =
  let reps = Array.make 5 0.0 in
  for r = 0 to 4 do
    let t0 = now_ns () in
    for _ = 1 to iters do
      sink := !sink + op ()
    done;
    let ns = (now_ns () -. t0) /. float_of_int (max iters 1) in
    reps.(r) <- ns
  done;
  median reps

let mbps size ns_per_op =
  if ns_per_op = 0.0 then 0.0
  else (float_of_int size /. (1024.0 *. 1024.0)) /. (ns_per_op /. 1e9)

let round2 f = float_of_int (int_of_float ((f *. 100.0) +. 0.5)) /. 100.0

(* Decode-only throughput on a provided raw-DEFLATE stream (fixed external
   encoder), so every decoder is measured on byte-identical input. Throughput is
   against the decoded (uncompressed) byte count. *)
let run_decode path =
  let comp = read_file path in
  let size = String.length (inflate comp) in
  let iters = iters_for size in
  let d_ns = median_ns_per_op iters (fun () -> String.length (inflate comp)) in
  if !sink = 0 then prerr_endline "unreachable";
  Printf.printf "{\"decompress_mbps\": %.2f, \"decoded_size\": %d}\n"
    (round2 (mbps size d_ns)) size

let () =
  if Array.length Sys.argv = 3 && String.equal Sys.argv.(1) "decode" then begin
    run_decode Sys.argv.(2);
    exit 0
  end;
  if Array.length Sys.argv <> 3 then begin
    prerr_endline "usage: bench <payload.bin> <level>  |  bench decode <stream.bin>";
    exit 2
  end;
  let path = Sys.argv.(1) in
  let level = int_of_string Sys.argv.(2) in
  let data = read_file path in
  let size = String.length data in
  let iters = iters_for size in

  (* Self-roundtrip check before timing. *)
  let comp = deflate data level in
  let back = inflate comp in
  if not (String.equal back data) then begin
    prerr_endline "roundtrip mismatch: inflate(deflate(data)) != data";
    exit 1
  end;

  let c_ns =
    median_ns_per_op iters (fun () -> String.length (deflate data level))
  in
  let d_ns =
    median_ns_per_op iters (fun () -> String.length (inflate comp))
  in

  if !sink = 0 then prerr_endline "unreachable";
  Printf.printf
    "{\"out_size\": %d, \"compress_mbps\": %.2f, \"decompress_mbps\": %.2f}\n"
    (String.length comp)
    (round2 (mbps size c_ns))
    (round2 (mbps size d_ns))

// Zig DEFLATE comparator for the lean-zip Track D dashboard.
//
// Uses the pure-Zig standard-library `std.compress.flate` (raw DEFLATE), built
// with Zig 0.14.1 — the last release before the 0.15 encoder refactor (whose
// `Compress.zig` is an unimplemented `@panic("TODO")`). Honours the shared
// comparator contract:
//
//   bench-zig <payload.bin> <level>  ->  stdout JSON
//   {"out_size": N, "compress_mbps": X, "decompress_mbps": Y}
//
// Timing mirrors ZipBenchReport.lean: median-of-5 reps, itersFor(size) iters per
// rep, throughput against the uncompressed byte count. Self-verifies its
// roundtrip before timing.
//
// Caveat: Zig's stdlib flate does NOT implement DEFLATE levels 1–3 ("a different
// algorithm … not implemented here", per std/compress/flate/deflate.zig), so we
// map requested levels 1–3 to the fastest real level it has (level_4); levels
// 4–9 map straight through. L1–L4 therefore coincide for Zig.
const std = @import("std");
const flate = std.compress.flate;

var sink: u64 = 0; // accumulates work so the optimizer can't elide timed calls

fn itersFor(size: usize) usize {
    if (size <= 16384) return 50;
    if (size <= 262144) return 10;
    if (size <= 1048576) return 3;
    return 1;
}

fn levelOf(n: u8) flate.deflate.Level {
    return switch (n) {
        1, 2, 3, 4 => .level_4,
        5 => .level_5,
        6 => .level_6,
        7 => .level_7,
        8 => .level_8,
        else => .level_9,
    };
}

fn deflate(alloc: std.mem.Allocator, data: []const u8, level: flate.deflate.Level) ![]u8 {
    var out = std.ArrayList(u8).init(alloc);
    var in = std.io.fixedBufferStream(data);
    try flate.compress(in.reader(), out.writer(), .{ .level = level });
    return out.toOwnedSlice();
}

fn inflate(alloc: std.mem.Allocator, comp: []const u8) ![]u8 {
    var out = std.ArrayList(u8).init(alloc);
    var in = std.io.fixedBufferStream(comp);
    try flate.decompress(in.reader(), out.writer());
    return out.toOwnedSlice();
}

fn median(xs: []u64) u64 {
    std.mem.sort(u64, xs, {}, std.sort.asc(u64));
    return xs[xs.len / 2];
}

fn mbps(size: usize, ns_per_op: u64) f64 {
    if (ns_per_op == 0) return 0;
    return (@as(f64, @floatFromInt(size)) / (1024.0 * 1024.0)) /
        (@as(f64, @floatFromInt(ns_per_op)) / 1e9);
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const alloc = gpa.allocator();

    const args = try std.process.argsAlloc(alloc);
    if (args.len != 3) {
        std.debug.print("usage: bench-zig <payload.bin> <level>\n", .{});
        std.process.exit(2);
    }
    const level = levelOf(try std.fmt.parseInt(u8, args[2], 10));
    const data = try std.fs.cwd().readFileAlloc(alloc, args[1], 1 << 30);
    const size = data.len;
    const iters = itersFor(size);

    const comp = try deflate(alloc, data, level);
    const back = try inflate(alloc, comp);
    if (!std.mem.eql(u8, back, data)) {
        std.debug.print("roundtrip mismatch: inflate(deflate(data)) != data\n", .{});
        std.process.exit(1);
    }

    var creps: [5]u64 = undefined;
    for (&creps) |*rep| {
        var timer = try std.time.Timer.start();
        var i: usize = 0;
        while (i < iters) : (i += 1) {
            const c = try deflate(alloc, data, level);
            sink +%= c.len;
            alloc.free(c);
        }
        rep.* = timer.read() / @max(iters, 1);
    }
    const c_ns = median(&creps);

    var dreps: [5]u64 = undefined;
    for (&dreps) |*rep| {
        var timer = try std.time.Timer.start();
        var i: usize = 0;
        while (i < iters) : (i += 1) {
            const d = try inflate(alloc, comp);
            sink +%= d.len;
            alloc.free(d);
        }
        rep.* = timer.read() / @max(iters, 1);
    }
    const d_ns = median(&dreps);

    if (sink == 0) std.debug.print("unreachable\n", .{});
    var buf: [256]u8 = undefined;
    const line = try std.fmt.bufPrint(&buf, "{{\"out_size\": {d}, \"compress_mbps\": {d:.2}, \"decompress_mbps\": {d:.2}}}\n", .{ comp.len, mbps(size, c_ns), mbps(size, d_ns) });
    try std.io.getStdOut().writeAll(line);
}

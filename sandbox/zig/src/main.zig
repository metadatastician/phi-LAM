const std = @import("std");
const policy = @import("policy.zig");

pub fn main() !void {
    var args = std.process.args();
    _ = args.next();
    const operation_text = args.next() orelse return error.MissingOperation;
    const operation = std.meta.stringToEnum(policy.Capability, operation_text) orelse
        return error.UnknownOperation;

    var grants: [4]policy.Capability = undefined;
    var grant_count: usize = 0;
    while (args.next()) |grant_text| {
        const grant = std.meta.stringToEnum(policy.Capability, grant_text) orelse
            return error.UnknownCapability;
        grants[grant_count] = grant;
        grant_count += 1;
    }

    const decision = policy.authorize(operation, grants[0..grant_count]);
    const stdout = std.fs.File.stdout().deprecatedWriter();
    try stdout.print("{s}\n", .{@tagName(decision)});
}

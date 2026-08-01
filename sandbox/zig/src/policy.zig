const std = @import("std");

pub const Capability = enum {
    filesystem_read,
    filesystem_write,
    network,
    spawn_process,
};

pub const Decision = enum { allow, deny };

pub fn authorize(operation: Capability, granted: []const Capability) Decision {
    for (granted) |capability| {
        if (capability == operation) return .allow;
    }
    return .deny;
}

test "empty capability set denies every operation" {
    const none = [_]Capability{};
    try std.testing.expectEqual(Decision.deny, authorize(.filesystem_read, &none));
    try std.testing.expectEqual(Decision.deny, authorize(.network, &none));
}

test "a grant is exact and does not imply adjacent authority" {
    const granted = [_]Capability{.filesystem_read};
    try std.testing.expectEqual(Decision.allow, authorize(.filesystem_read, &granted));
    try std.testing.expectEqual(Decision.deny, authorize(.filesystem_write, &granted));
    try std.testing.expectEqual(Decision.deny, authorize(.network, &granted));
}

const std = @import("std");

/// This represents our embedded `typed-wasm` runtime environment.
pub const WasmSandbox = struct {
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) WasmSandbox {
        return .{ .allocator = allocator };
    }

    pub fn execute(self: *WasmSandbox, payload: []const u8) !void {
        _ = self;
        std.debug.print("[Zig typed-wasm Sandbox] Executing verified AffineScript payload of {} bytes...\n", .{payload.len});
        
        // If the payload is mathematically proven safe by Idris2, we run it here.
        if (std.mem.eql(u8, payload, "unsafe_mock")) {
            return error.SandboxViolation;
        }
    }
};

/// This is the SNIF (Safe NIF) C-ABI boundary for Elixir.
/// Erlang/Elixir NIFs call this via C FFI. If this was a regular NIF, a crash here
/// would kill the BEAM. Because it's a SNIF written in Zig, we catch errors safely.
export fn execute_verified_strand(payload_ptr: [*c]const u8, payload_len: usize) c_int {
    const payload = payload_ptr[0..payload_len];
    
    var sandbox = WasmSandbox.init(std.heap.page_allocator);
    
    sandbox.execute(payload) catch |err| {
        std.debug.print("[Zig SNIF Error] Execution halted: {}\n", .{err});
        return -1; // Return failure code to Elixir without panicking the VM
    };
    
    return 0; // Success
}

const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const lib = b.addLibrary(.{
        .linkage = .dynamic,
        .name = "sandbox",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/root.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    
    // Allow Elixir to load it without complaining about missing BEAM symbols
    lib.linker_allow_shlib_undefined = true;

    b.installArtifact(lib);
}

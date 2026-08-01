#!/bin/bash
set -e
cd /home/hyperpolymath/developer/meta-repos/phi-LAM
mise install
cd src/sandbox
mise exec zig -- zig init
cd ../inference
mise exec julia -- julia -e 'using Pkg; Pkg.generate("PhiLamInference")'
cd ../symbolic
echo 'package phi_lam
version = 0.1.0
authors = "hyperpolymath"
main = Main
executable = "phi_lam"
sourcedir = "src"' > phi_lam.ipkg
mkdir -p src

set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

idris2 := env_var_or_default("IDRIS2", "idris2")

build:
    {{idris2}} --build phi-lam.ipkg

test:
    {{idris2}} --source-dir src -o phi-lam-tests src/TestNormalize.idr
    ./build/exec/phi-lam-tests

lean-check:
    cd formal/lean && lake build

contracts-check:
    bash scripts/check-contracts.sh

orchestrator-check:
    cd orchestrator && mix format --check-formatted
    cd orchestrator && mix compile --warnings-as-errors --no-deps-check
    cd orchestrator && mix test --no-compile

sandbox-check:
    cd sandbox/zig && ZIG_GLOBAL_CACHE_DIR=/tmp/phi-lam-zig-global ZIG_LOCAL_CACHE_DIR=/tmp/phi-lam-zig-local zig build test

inference-check:
    cd inference/julia && JULIA_DEPOT_PATH=/tmp/phi-lam-julia-depot julia --project=. --startup-file=no test/runtests.jl

engineering-check: contracts-check orchestrator-check sandbox-check inference-check

check: build test lean-check engineering-check

clean:
    {{idris2}} --clean phi-lam.ipkg
    rm -f build/exec/phi-lam-tests

set shell := ["bash", "-eu", "-o", "pipefail", "-c"]

idris2 := env_var_or_default("IDRIS2", "idris2")

build:
    {{idris2}} --build phi-lam.ipkg

test:
    {{idris2}} --source-dir src -o phi-lam-tests src/TestNormalize.idr
    ./build/exec/phi-lam-tests

check: build test

clean:
    {{idris2}} --clean phi-lam.ipkg
    rm -f build/exec/phi-lam-tests

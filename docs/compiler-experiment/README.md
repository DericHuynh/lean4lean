# Experimental Lean resource compiler

This branch develops a separate Lean 4 resource-analysis and compilation experiment while preserving upstream `lean4lean` checker behavior.  The initial stage is an executable Lean model and formally checked, model-scoped proofs.  It is **not** yet a certified backend, a replacement for the Lean compiler, or a proof about emitted machine code.

The pinned toolchain is `leanprover/lean4:v4.33.0-rc2`.  New code is isolated under `Lean4LeanCompiler/`.  Build targets and tests are added separately; upstream default targets remain unchanged.

Safety policy: unsupported runtime constructs, uncertified calls, borrowing escapes, uninitialized output bytes, shared reuse, and allocating fallbacks under no-allocation contracts are rejected in checked mode. The executable model deliberately treats actual runtime allocation identity, uniqueness and foreign primitives as assumptions until validated against Lean's real ABI.

Verification phases: model transition safety and resource-count checking; source-LCNF adaptation; certificate checking tied to actual declarations; differential tests against stock compiler; native backend in a later milestone. We do not claim coverage for omitted phases.

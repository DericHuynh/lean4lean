# Resource compiler verification ledger (2026-10-10)

## Supported functionality

- **Source examples:** ordinary Lean ByteArray copying, four-byte reversal, fixed-size destination write, and List UInt8 mapping. Stock Lean handles all code generation; the reference module is compiled before experimental passes are installed.
- **Integrated experimental compiler pass:** an opt-in `@[cpass]` for functions in `Lean4LeanCompiler.Examples` removes zero-count explicit RC instructions, if encountered, after explicit RC insertion. A separate audit pass records already-inferred borrowed parameters. The pass does not yet infer new lifetimes, destination placement, or FP² reuse.
- **Checked resource model:** flat, first-order byte storage, nested borrow counter, distinct fresh destination, scalar SSA register loads, capacity-bounded initialization, and uniquely owned reuse of childless flat storage. A no-allocation guarantee covers **only the explicitly delimited writer region**. Final output allocation before this region is reported outside it.

## Formal claims (Lean 4 files)

- `check_sound`: acceptance of a **specific modeled operation list, initial state, and budget** implies some final model state satisfying the checked contract.
- `run_eraseNops`: deleting modeled no-op instructions preserves the exact option result of the model runner (including failures and modeled costs).
- `check_eraseNops`: the model resource check is invariant under that deletion.
- `copyFour_bytes`, `copyFour_no_region_alloc`, `copyFour_preserves_source`: byte-level correspondence, metering, and owner preservation for exactly four bytes in the model.
- `reverseFour_bytes`, `reverseFour_no_region_alloc`, `reverseFour_shared_rejected`: byte-level correspondence and uniqueness precondition in the model.

The model makes source ownership and uniqueness explicit **inputs**; it does not prove those inputs arise from a Lean runtime pointer. These model theorems do not prove correctness of the separate LCNF transformation. A `#print axioms` audit is included in the Lean proof module. No new `sorry`, `admit`, or program-correctness axioms are intentionally introduced.

## Unverified boundaries

| Boundary | Status |
|---|---|
| Model runner and proof obligations | Lean source authored; CI compile must be checked |
| Import from elaborated Lean declaration | **Not implemented** |
| Correspondence of modeled operation list to Lean impure LCNF | **Unproved** |
| Runtime RC count/uniqueness, shared descendants and storage capacity | **Assumptions; not certified** |
| Correctness of reset/reuse, specialization, closure conversion and erasure | **Stock Lean trust boundary** |
| Source examples versus stock behavior | Differential executable test, not a semantic proof |
| Backend / C or LLVM / assembler / native bytes | **Stock Lean only, not verified** |
| Physical allocations, bytes copied, peak RSS, stack | **Not yet instrumented or measured** |
| Higher-order functions, arbitrary recursion, IO, exceptions, unsafe, FFI | **Unsupported in model** |

## Reproduce

Use the checkout's pinned `leanprover/lean4:v4.33.0-rc2` toolchain:

```sh
lake build Lean4LeanCompiler
lake build lean4leanCompilerDemo
lake exe lean4leanCompilerDemo
lake build Lean4Lean
lake build lean4lean
lake build Lean4Lean.Theory
lake build Lean4Lean.Verify
lake build Lean4Lean.Tests
```

If a model theorem fails, the branch does not meet its verification checkpoint. If the differential test fails, revert or fix the LCNF rewrite. No certificate is emitted for regular Lean functions on this branch.

## Next substantial milestone

Build a pinned-version `Lean.Compiler.LCNF.Decl` adapter and evidence checker tied to actual post-erasure instructions; validate borrow liveness/ownership, storage disjointness, and destination initialization. This is necessary before any verified compiler optimization or no-allocation claim for an ordinary Lean declaration. Then add explicit physical allocation instrumentation and benchmark release builds against optimized stock Lean. Do not silently accept stock fallback under a strict resource contract.

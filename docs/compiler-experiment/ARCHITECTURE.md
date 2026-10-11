# Experimental compiler architecture and primary sources

## Checkout facts

- The authoritative compiler checkout is the **fork's pinned** Lean `leanprover/lean4:v4.33.0-rc2` (from `lean-toolchain`). The larger `DericHuynh/lean4` fork is not automatically ABI-compatible with that pin.
- Existing Lean4Lean goals and `lean4lean` CLI are preserved. The new component lives under `Lean4LeanCompiler/`, has its own Lake library and demo executable, and does not modify the kernel checker. Upstream verification files include pre-existing admissions; an unrelated new proof module must not be credited with eliminating those.
- The example declarations are ordinary Lean definitions, not handwritten AST inputs. `Reference.lean` is compiled without the experimental pass. `Examples.lean` imports the compiler hook, which is scoped by declaration name.

## Pinned compiler integration

Source inspection of Lean v4.33.0-rc2 shows the following pipeline:

```
Lean Expr / elaboration / specialization
    -> LCNF base and mono passes
    -> toImpure
    -> pushProj
    -> insertResetReuse
    -> elimDeadVars; simpCase
    -> inferBorrow
    -> explicitBoxing
    -> explicitRc
    -> expandResetReuse
    -> coalesceRc
    -> [experimental audit hook]
    -> pushProj; detectSimpleGround; toposortPass
    -> saveImpure
    -> IR.toIR; IR.compile
    -> stock C/LLVM backend and Lean runtime
```

The experimental zero-count RC cleanup is installed **before `coalesceRc`**; it does not replace `inferBorrow`, `explicitRc`, or `reset/reuse`. This matters: stock Lean already performs substantial borrowing and reuse optimization, so future benchmarks must compare against the actual optimized stock compiler.

Primary pinned source references:
- [Lean4 LCNF pass order](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/Passes.lean)
- [LCNF typed IR and constructors](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/Basic.lean)
- [Borrowing inference](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/InferBorrow.lean)
- [Reset and reuse](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/ResetReuse.lean)
- [RC insertion](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/ExplicitRC.lean)
- [Source-to-IR lowering](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/IR/ToIR.lean)
- [IR and emitter](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/IR/Basic.lean)
- [Lean runtime object model](https://github.com/leanprover/lean4/tree/v4.33.0-rc2/src/runtime)

## Model memory discipline

- Values: childless, flat byte payloads and unboxed UInt8 registers only.
- Source: live owner plus nested-borrow count and a unique-storage assumption, or dropped.
- Destination: absent; allocated with capacity and initialized prefix proof; or published with length equal to capacity.
- Lifetime: owner drop prohibited while borrow count is nonzero. Borrowed loads require a live owner. Consuming reuse requires zero live borrows, unique source storage and no competing destination.
- Destination: only appends within capacity are possible, and publication requires every observable output byte initialized.
- Resource budget: total allocations, total allocated bytes, **separately** writer-region allocations/bytes, and reuse count.
- Precision: all sizes are mathematical Nat, so physical address overflow/allocator layout are *not* covered. Region counts are model events and say nothing about the real allocator unless correspondence is separately established.

## Untrusted optimizer / small trusted checker direction

The current trusted checker evaluates the exact model instruction list and directly tests its final budget and lifetime properties. Its soundness theorem is relative to those model semantics. In a later increment, a source adapter must *derive* the model certificate from actual LCNF operations and a small verified validator must check representation/layout, initialization, ownership and call-summary effects. Merely putting a Lean declaration's name beside a model trace does not prove that the trace describes it.

Morphic-inspired mode/lifetime inference, FP² storage credits and destination passing will share a common certificate. Certificate invalidation after rewrites is mandatory, especially when lifetime, aliasing and reuse arrangements change.

## Literature

- [Counting Immutable Beans](https://arxiv.org/abs/1908.05647)
- [Morphic compiler](https://github.com/morphic-lang/morphic)
- [Fully-Automatic Type Inference for Borrows with Lifetimes](https://doi.org/10.1145/3798221)
- [FP²: Fully In-Place Functional Programming](https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf)
- [Destination Calculus](https://arxiv.org/abs/2503.07489)
- [Safe destination passing](https://arxiv.org/abs/2601.08529)

These papers are research inputs, not proof that the current LCNF cleanup implements their algorithms. This work must gradually replace stock operations rather than claim the current hook is a new verified compiler.

# Experimental real-LCNF-to-ELF scalar compiler (checkpoint)

## What this implements

The previous fixed proof-registered kernel backend emitted native templates
selected by Lean source-level theorems. This new compiler path obtains the
selection from **actual Lean 4 compiler IR**.

1. Lean elaborates and compiles an ordinary declaration from
   Lean4LeanCompiler/NativeExamples.lean through the pinned v4.33.0-rc2 compiler.
2. An opt-in cpass runs on the compiler's **impure LCNF declarations**, after
   stock reset/reuse, borrowing, RC insertion, and RC coalescing.
3. The LCNF recognizer accepts only safe, nonrecursive, scalar UInt64 direct
   returns of a declared input parameter, with 1 or 2 recognized scalar
   parameters. It rejects unsupported calls, branches, effects, constructors,
   RC, aliased parameters and unsafe/partial code. It cannot silently fall back.
4. The pass exports a typed argument-register selection via a
   SimplePersistentEnvExtension recorded into the declaring module's .olean.
5. A separate Lean CLI imports the module and requires exactly one corresponding
   checked export, then emits native machine bytes directly as an ELF64 x86-64
   relocatable object; no generated C/Rust/LLVM/assembly intermediate language.
6. A C harness is used **only as an independent executable ABI test**. It links
   the emitted object and checks 200,000 seeded scalar inputs and edge cases.

The supported current example is a UInt64 identity. This is intentionally tiny
but provides a complete *source declaration → actual compiler IR → native object*
route that previously did not exist.

## Commands

Use the existing pinned lean-toolchain and Linux/x86-64:

    lake build Lean4LeanCompiler.NativeExamples lean4leanFromLCNF
    mkdir -p .lake/build/native
    lake exe lean4leanFromLCNF .lake/build/native/from_lcnf.o
    readelf -hW -SW -sW .lake/build/native/from_lcnf.o
    objdump -dr .lake/build/native/from_lcnf.o
    cc -std=c11 -O3 -fno-lto -Wall -Wextra -Werror -Wl,-z,noexecstack \
      tests/native-from-lcnf.c .lake/build/native/from_lcnf.o \
      -o .lake/build/native/from-lcnf-test
    .lake/build/native/from-lcnf-test

## What is actually proved

- For the recognized register-choice vocabulary, encode/decode round-trip and
  register-value semantics are checked by Lean theorems.
- ELF layout consistency and exact text-byte extraction are checked by Lean
  theorems for each supported register selection.
- The ordinary Lean scalar function's logical output equals the modeled register
  return, checked with a source-level theorem.
- Existing Lean resource model/strict-LCNF-site proofs remain independent.

## Not yet established

- A verified *general* LCNF operational semantics or trusted proof of the
  translator's arbitrary-input soundness.
- Correctness of the stock erasure/lowering pipeline and runtime ABI against
  the mathematical Lean declarations.
- CPU, linker, loader, executable memory and all-of-ISA semantics.
- Resource guarantees for real Lean heap/RC operations.
- General arithmetic, direct calls or branch lowering from arbitrary LCNF.
- Faster compilation of the Lean 4 language itself. Current benchmarks only
  show a workload-specific runtime improvement for a distinct proof-selected
  serialization rewrite.

The persistent .olean summary is produced only by the source-bound compiler
pass; it is not a semantic proof of .olean serialization itself. Artifact
tampering and stale dependency binaries require separate validation and are
outside the current proof. Unsupported strict compilation fails explicitly.

## Reference implementations

- Pinned compiler pass manager:
  https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/PassManager.lean
- Pinned impure-LCNF:
  https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/Basic.lean
- Persistent environment extension API:
  https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/EnvExtension.lean
- Pinned pass ordering:
  https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/Passes.lean
- SysV x86-64 ABI:
  https://refspecs.linuxfoundation.org/elf/x86_64-abi-0.99.pdf
- ELF gABI:
  https://gabi.xinuos.com/v42/elf/03-sheader.html

This does not implement full Morphic inference, FP2 resource credits, or
destination-passing for arbitrary Lean declarations; see the corresponding
research and verification ledgers before interpreting any result as certified.

# Direct-native compiler milestone: x86-64 Linux ELF

Status: working restricted native backend, **not a verified full Lean compiler**. It is implemented in Lean 4 and retains the pinned Lean v4.33.0-rc2 version. The preexisting checker CLI is preserved.

## Actual compiler path

1. Ordinary Lean source declarations: Native.sourceAdd64 (UInt64 addition) and Reference.writeFourInto (ByteArray destination writing).
2. Each operation has a Lean proof-carrying registration, CertifiedAdd.sourceCorrect or CertifiedCopy4.sourceCorrect. The compiler only emits the selected fixed opcode templates after these Lean declarations/proofs compile.
3. Native.ISA defines an instruction subset, instruction bytes, modeled register/memory behavior, and Lean theorems checking their relationship.
4. Native.ELF writes actual ELF64 section headers, machine bytes and symbol metadata from Lean 4. No generated C/Rust/LLVM IR or assembler is an intermediate compilation target.
5. Lake executable lean4leanNative writes a linkable object file. C is used *only as a test harness*.

Reproduce on Linux/x86-64:

    lake build Lean4LeanCompiler lean4leanNative lean4leanCompilerDemo
    mkdir -p .lake/build/native
    lake exe lean4leanNative .lake/build/native/l4lc_kernels.o
    readelf -hW -SW -sW .lake/build/native/l4lc_kernels.o
    objdump -dr .lake/build/native/l4lc_kernels.o
    cc -std=c11 -O3 -fno-lto -Wall -Wextra -Werror -Wl,-z,noexecstack tests/native-elf-abi.c .lake/build/native/l4lc_kernels.o -o .lake/build/native/native-abi-test
    .lake/build/native/native-abi-test
    .lake/build/native/native-abi-test --bench

## Binary and ABI

The original leaf-only object was 552 bytes. The relocation-capable object is 712 bytes, ELF64 little-endian ET_REL, x86-64, with .text, .symtab, .strtab and .shstrtab sections and two exported symbols. It includes an inter-function call and one R_X86_64_PLT32 ELF relocation.

| Symbol | SysV AMD64 calling convention | Preconditions |
|---|---|---|
| l4lc_add64 | rdi, rsi: uint64 → rax: uint64 | Wrapping addition modulo 2^64 |
| l4lc_copy4 | rdi: readable uint8*, rsi: writable uint8* → void | Four readable and four writable bytes, live/valid for the call |
| l4lc_add_then_inc | rdi, rsi: uint64 → rax: uint64 | Internally CALL l4lc_add64 with 16-byte stack alignment, then increment |

Copy4 loads the entire 32-bit value into EAX before writing it into the destination. The emitted code does not dynamically check bounds or allocation ownership. The native ABI does not accept Lean ByteArray objects directly: the caller passes raw native pointers. Test harness copy cases include valid pointer overlaps, but their physical alias/ownership properties are *not* proved by the current list-based model.

## Verification coverage

| Claim | Evidence |
|---|---|
| Modeled add and copy match theorem-registered Lean source values | Native.modeledAdd_matchesSource and modeledCopy_matchesSource, checked by Lean, no axioms |
| Correctness of the limited modeled opcode decoding/execution | Native.ISA.addCode_correct, copyCode_exact, decodeAdd_emitted and decodeCopy_emitted, kernel checked |
| Emitted text matches exact modeled opcodes | Native.ELF.code_span_correct, emitted_add_opcode and emitted_copy_opcode, kernel checked |
| ELF object metadata internal layout | Native.ELF.layoutValid_true and magic_correct, kernel checked |
| Real CPU/linker/runtime behavior | Native executable tests only, **not formally verified** |
| General Lean AST/LCNF importer, erasure and machine semantics | Not implemented/proved |
| Physical RC/heap/stack budget guarantees | Not implemented/proved |
| Full native Lean compiler / bootstrap / global compilation speedup | Not demonstrated |

A theorem about modeled opcodes does not prove the real processor's instruction semantics, the ELF loader, machine memory safety, or arbitrary Lean compilation.

## Actual measured performance

[First passing native CI run](https://github.com/DericHuynh/lean4lean/actions/runs/38105131514): five repetitions of 8,000,000 scalar calls with a shared function-pointer driver, x86-64 GitHub runner, C compiled with -O3 -fno-lto. Measured native elapsed / optimized-C elapsed: **0.991, 0.998, 1.002, 0.997, 0.999**. This is near equality, not a material performance improvement and **not a Lean compiler build benchmark**. Source-level verified Join3 benchmarks are tracked separately.

Native integration validation: 200,000 randomized arithmetic cases, all selected boundary combinations, and 40,000 randomized byte-copy cases including overlapping pointers. The native object is linked and executed through cc, and examined using readelf, nm and objdump. These tests validate the intended ABI under the specific Linux environment, not all CPUs or runtimes.

## Reference implementations

- Lean LCNF pass order, including stock borrowing/reset/reuse: https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/LCNF/Passes.lean
- Proof-guided csimp substitution: https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Compiler/CSimpAttr.lean
- System V AMD64 ABI: https://refspecs.linuxfoundation.org/elf/x86_64-abi-0.99.pdf
- ELF section headers: https://gabi.xinuos.com/v42/elf/03-sheader.html
- Morphic lifetimes and borrowing: https://github.com/morphic-lang/morphic and https://doi.org/10.1145/3798221
- FP2 fully in-place functional programming: https://www.microsoft.com/en-us/research/wp-content/uploads/2023/05/fbip.pdf
- Counting Immutable Beans: https://arxiv.org/abs/1908.05647
- Frame-limited reuse: https://www.microsoft.com/en-us/research/publication/reference-counting-with-frame-limited-reuse-extended-version/
- Destination Calculus: https://arxiv.org/abs/2503.07489
- Safe destination passing: https://arxiv.org/abs/2601.08529

These are *research directions*, not formal certificates for the current implementation. Remaining engineering priority: import actual Lean LCNF for the supported fragment, reject all unvalidated paths in strict mode, carry certificates through transformations, add relocations/interoperability, and benchmark real Lean code compilation and execution against optimized stock Lean rather than a fictional naïve baseline.

## Inter-function call and relocation milestone

The ELF exporter adds a complete .rela.text section and emits one R_X86_64_PLT32 relocation (symbol index 2; addend -4; displacement offset 15 within .text). It emits a call wrapper that aligns the System V stack, calls the certified addition function and restores stack state. Lean proves a small CALL/stack-state model, the source function equality, and the relocation payload bytes. The external system linker resolves this relocation and the linked executable is tested. The machine semantics and linker/loader remain outside the Lean proof boundary. Reference: System V AMD64 ABI relocation types and ELF gABI; see primary sources above.

/*
 * Independent ABI/differential test for the direct ELF object emitted in Lean.
 * This is a TEST HARNESS, not generated C and not an intermediate backend.
 * Compile on x86_64 Linux with a normal C compiler and link the generated .o.
 * No compiler-correctness or memory-safety theorem is inferred from the test.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <inttypes.h>
#include <stdlib.h>

extern uint64_t l4lc_add64(uint64_t a, uint64_t b);
extern void l4lc_copy4(const unsigned char *src, unsigned char *dst);

#if defined(__GNUC__) || defined(__clang__)
#define NOINLINE __attribute__((noinline))
#else
#define NOINLINE
#endif

NOINLINE uint64_t reference_add64(uint64_t a, uint64_t b) { return a + b; }

static uint64_t seed = UINT64_C(0x87178291199c379d);
static uint64_t random64(void) {
  seed ^= seed << 13;
  seed ^= seed >> 7;
  seed ^= seed << 17;
  return seed;
}

static int unit_tests(void) {
  static const uint64_t boundaries[] = {
    UINT64_C(0), UINT64_C(1), UINT64_MAX, UINT64_MAX-1,
    UINT64_C(0x8000000000000000), UINT64_C(0x7fffffffffffffff)
  };
  for (size_t i = 0; i < sizeof(boundaries)/sizeof(boundaries[0]); ++i)
    for (size_t j = 0; j < sizeof(boundaries)/sizeof(boundaries[0]); ++j)
      if (l4lc_add64(boundaries[i], boundaries[j]) !=
          reference_add64(boundaries[i], boundaries[j])) return 1;

  for (unsigned i=0; i<200000; ++i) {
    uint64_t a = random64(), b = random64();
    if (l4lc_add64(a,b) != reference_add64(a,b)) return 2;
  }

  /* Each native call receives 4 readable and 4 writable bytes.
   * Snapshot expected bytes before a potentially overlapping write.
   * No out-of-bounds pointer reaches the native object. */
  for (unsigned iter=0; iter<40000; ++iter) {
    unsigned char buf[32], expected[32], snapshot[4];
    for (size_t i=0;i<sizeof(buf);++i) buf[i] = (unsigned char) random64();
    memcpy(expected, buf, sizeof(buf));
    size_t srcOff = (size_t)(random64()%29);
    size_t dstOff = (size_t)(random64()%29);
    memcpy(snapshot, expected+srcOff, 4);
    memcpy(expected+dstOff, snapshot, 4);
    l4lc_copy4(buf+srcOff, buf+dstOff);
    if (memcmp(buf,expected,sizeof(buf))!=0) {
      fprintf(stderr, "copy4 mismatch src=%zu dst=%zu\n",srcOff,dstOff);
      return 3;
    }
  }
  return 0;
}

static volatile uint64_t consumed;

/* Both implementations are invoked via a function pointer from the
 * identical driver. Prevent inlining and LTO for a fair call/ABI baseline.
 * The baseline is optimized C, NOT stock Lean. */
static NOINLINE uint64_t timed(uint64_t(*fn)(uint64_t,uint64_t),uint64_t iterations,
                               double *elapsed_ns) {
  struct timespec start, end;
  if (clock_gettime(CLOCK_MONOTONIC,&start)) return 0;
  uint64_t value = UINT64_C(0xcafe203407187fff);
  for (uint64_t i=0;i<iterations;i++)
    value = fn(value+i, i*UINT64_C(0x9e3779b97f4a7c15));
  if (clock_gettime(CLOCK_MONOTONIC,&end)) return 0;
  consumed ^= value;
  *elapsed_ns =
    (double)(end.tv_sec-start.tv_sec)*1e9+
    (double)(end.tv_nsec-start.tv_nsec);
  return value;
}

int main(int argc, char **argv) {
  int rc=unit_tests();
  if (rc) {
    fprintf(stderr,"native ELF ABI test failure: %d\n",rc);
    return rc;
  }
  puts("PASS: native ELF ABI, 200000 arithmetic cases, 40000 copy/overlap cases");
  if (argc>1 && strcmp(argv[1],"--bench")==0) {
    uint64_t iterations=8000000;
    for (unsigned rep=0;rep<5;rep++) {
      double stockNs=0,nativeNs=0;
      uint64_t stock=timed(reference_add64,iterations,&stockNs);
      uint64_t native=timed(l4lc_add64,iterations,&nativeNs);
      if (stock!=native) return 5;
      printf("benchmark rep=%u iterations=%" PRIu64
             " referenceC=%.1f ns native=%.1f ns nativeOverReferenceC=%.3f consumed=%" PRIu64 "\n",
             rep,iterations,stockNs,nativeNs,nativeNs/stockNs,(uint64_t)consumed);
    }
    puts("NOTE: comparison is to optimized C, not a stock Lean compiler workload");
  }
  return 0;
}

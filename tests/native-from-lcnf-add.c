/*
 * Independent ABI test of an actual Lean-LCNF-selected addition function.
 * C tests the emitted native bytes; C is never a compiler intermediate.
 */
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>

extern uint64_t l4lc_add_from_lcnf(uint64_t, uint64_t);

int main(void) {
  uint64_t seed = UINT64_C(0xa07576a179838252);
  const uint64_t bounds[] = {UINT64_C(0), UINT64_C(1), UINT64_MAX,
      UINT64_C(0x7fffffffffffffff), UINT64_C(0x8000000000000000)};
  for (unsigned i = 0; i < sizeof(bounds)/sizeof(bounds[0]); ++i)
    for (unsigned j = 0; j < sizeof(bounds)/sizeof(bounds[0]); ++j)
      if (l4lc_add_from_lcnf(bounds[i], bounds[j]) !=
          (uint64_t)(bounds[i] + bounds[j])) return 1;
  for (unsigned i = 0; i < 200000; ++i) {
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
    uint64_t a=seed;
    seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17;
    uint64_t b=seed;
    const uint64_t expected=a+b;
    const uint64_t actual=l4lc_add_from_lcnf(a,b);
    if (actual != expected) {
      fprintf(stderr,"LCNF native addition mismatch i=%u actual=%" PRIu64 " expected=%" PRIu64 "\n",i,actual,expected);
      return 2;
    }
  }
  puts("PASS: real Lean LCNF UInt64.add native ABI: 200000 randomized pairs");
  return 0;
}

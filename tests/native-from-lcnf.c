/*
 * Independent ABI test, not a compiler intermediate. Every call receives
 * a valid scalar; no raw pointer or Lean object representation is involved.
 */
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
extern uint64_t l4lc_from_lcnf(uint64_t);

int main(void) {
  uint64_t seed = UINT64_C(0x0f1e2d3c4b5a6978);
  const uint64_t edge[] = {
    UINT64_C(0), UINT64_C(1), UINT64_MAX,
    UINT64_C(0x7fffffffffffffff), UINT64_C(0x8000000000000000)
  };
  for (unsigned j=0; j<sizeof(edge)/sizeof(edge[0]); ++j)
    if (l4lc_from_lcnf(edge[j]) != edge[j]) return 1;
  for (unsigned i=0; i<200000; ++i) {
    seed ^= seed << 13;
    seed ^= seed >> 7;
    seed ^= seed << 17;
    if (l4lc_from_lcnf(seed) != seed) {
      fprintf(stderr,"identity mismatch at i=%u expected=%" PRIu64 "\n",i,seed);
      return 2;
    }
  }
  puts("PASS: actual LCNF native identity ABI, 200000 randomized calls");
  return 0;
}

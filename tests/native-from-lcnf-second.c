/*
 * Independent executable ABI test for actual LCNF return-of-second-argument.
 * C only tests native object bytes produced directly by the Lean backend.
 */
#include <stdint.h>
#include <stdio.h>
#include <inttypes.h>
extern uint64_t l4lc_from_lcnf(uint64_t, uint64_t);

int main(void) {
  uint64_t seed = UINT64_C(0xe3b0c44298fc1c14);
  const uint64_t edge[] = {
    UINT64_C(0), UINT64_C(1), UINT64_MAX,
    UINT64_C(0x7fffffffffffffff), UINT64_C(0x8000000000000000)
  };
  for (unsigned i = 0; i < sizeof(edge)/sizeof(edge[0]); ++i)
    for (unsigned j = 0; j < sizeof(edge)/sizeof(edge[0]); ++j)
      if (l4lc_from_lcnf(edge[i],edge[j]) != edge[j]) return 1;
  for (unsigned i=0; i<200000; ++i) {
    seed ^= seed << 13;
    seed ^= seed >> 7;
    seed ^= seed << 17;
    uint64_t a=seed;
    seed ^= seed << 13;
    seed ^= seed >> 7;
    seed ^= seed << 17;
    uint64_t b=seed;
    if (l4lc_from_lcnf(a,b) != b) {
      fprintf(stderr,"second-argument mismatch i=%u value=%" PRIu64 "\n",i,b);
      return 2;
    }
  }
  puts("PASS: actual two-argument LCNF native ABI, 200000 randomized cases");
  return 0;
}

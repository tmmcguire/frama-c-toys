#include <string.h>

/*
 * frama-c -wp -wp-rte -wp-print brute-force.c
 */

/*
 * Search for needile in haystack, using a brute force algorithm.
 *
 * Expected complexity is O(n*h), where n in the length of the needle and
 * h is the length of the haystack.
 */
/*@
 requires \valid(needle + (0 .. n-1)) && 0 <= n < INT_MAX;
 requires \valid(haystack + (0 .. h-1)) && 0 <= h < INT_MAX;
 requires n <= h;
 */
int
brute_force (char *needle, int n, char *haystack, int h)
{
  int i, j;

  /* Searching */
  /*@
   loop assigns i, j;
   loop invariant 0 <= j <= (h-n) + 1;
   */
  for (j = 0; j <= h - n; ++j) {
    /*@
     loop assigns i;
     loop invariant 0 <= i <= n;
    */
    for (i = 0; i < n && needle[i] == haystack[i + j]; ++i);
    if (i >= n) {
      return j;
    }
  }
  return -1;
}

/*
 * Current valid properties:
 * - loop assignments (2)
 * - x <= 2147483647
 * - i <= 2147483646
 * - j <= 2147483646
 * - 0 <= n
 * - n <= (2147483648 + h)
 * - (-1) <= j (outer loop invariant)
 * - n <= (1 + h) (outer loop invariant)
 * - (-1) <= i
 * - (-2147483648) <= x
 * - valid_rd(Malloc_0, a, 1)
 * - valid_rd(Malloc_0, shift_sint8(haystack_0, to_sint32(x)), 1)
 * - h <= (2147483647 + n)
 */
/*
 * Current invalid properties:
 */

#include <string.h>

/*
 * Search for needile in haystack, using a brute force algorithm.
 *
 * Expected complexity is O(n*h), where n in the length of the needle and
 * h is the length of the haystack.
 */
/*@
 requires \valid(needle + (0 .. n-1)) && n < INT_MAX;
 requires \valid(haystack + (0 .. h-1)) && h < INT_MAX;
 requires n <= h;
 */
int
brute_force (char *needle, int n, char *haystack, int h)
{
  int i, j;

  /* Searching */
  /*@
   loop assigns i,j;
   */
  for (j = 0; j <= h - n; ++j) {
    /*@
     loop assigns i;
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
 * - x <= 2147483647, line 22
 * - i <= 2147483646, line 22
 * - n <= (2147483648 + h), line 18
 */
/*
 * Current invalid properties:
 * - h <= (2147483647 + n), line 18
 * - valid_rd(Malloc_0, a, 1), line 22
 * - valid_rd(Malloc_0, shift_sint8(haystack_0, to_sint32(x)), 1), line 22
 * - (-2147483648) <= x, line 22
 * - j <= 2147483646, line 18
 */

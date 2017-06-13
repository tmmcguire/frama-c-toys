#include <stdio.h>
#include <string.h>

/*
 * frama-c -wp -wp-rte -wp-print brute-force.c
 *
 * gcc -o brute-force -DMAIN -Wall brute-force.c
 */

/*@
  // There is a partial match of the needle at location loc in the
  // haystack, of length len.
  predicate partial_match_at(char *needle, char *haystack, int loc, int len) =
    \forall int i; 0 <= i < len ==> needle[i] == haystack[loc + i];
 */

/*@
  // There is a complete match of the needle at location loc in the
  // haystack.
  predicate match_at(char *needle, int n, char *haystack, int h, int loc) =
    \valid(needle + (0 .. n-1)) && 0 <= n < INT_MAX &&
    \valid(haystack + (0 .. h-1)) && 0 <= h < INT_MAX &&
    n <= h && loc <= h - n &&
    partial_match_at(needle, haystack, loc, n);
 */

/*
 * Search for needile in haystack, using a brute force algorithm.
 *
 * Returns the offset of the needle in the haystack or -1 if the needle is
 * not found.
 *
 * Expected complexity is O(n*h), where n in the length of the needle and
 * h is the length of the haystack.
 */
/*@
 requires \valid(needle + (0 .. n-1)) && 0 <= n < INT_MAX;
 requires \valid(haystack + (0 .. h-1)) && 0 <= h < INT_MAX;
 requires n <= h;
 assigns \nothing;
 ensures -1 <= \result <= (h-n);
 behavior success:
    ensures \result >= 0 ==> match_at(needle, n, haystack, h, \result);
 behavior failure:
    ensures \result == -1 ==>
      \forall int i; 0 <= i < h ==>
        !match_at(needle, n, haystack, h, i);
 */
int
brute_force (char *needle, int n, char *haystack, int h)
{
  int i, j;

  /* Searching */
  /*@
    loop assigns i, j;
    loop invariant 0 <= i <= (h-n) + 1;
    loop invariant \forall int k; 0 <= k < i ==>
      !match_at(needle, n, haystack, h, k);
   */
  for (i = 0; i <= h - n; ++i) {
    /* Check for a match at i */
    /*@
      loop assigns j;
      loop invariant 0 <= j <= n;
      loop invariant partial_match_at(needle, haystack, i, j);
    */
    for (j = 0; j < n && needle[j] == haystack[j + i]; ++j);
    if (j >= n) {
      return i;
    }
  }
  return -1;
}

/*
 * Current valid properties:
 * - function assignments (6)
 * - loop assignments (2)
 * - invariant establishment (2)
 * - x <= 2147483647
 * - j <= 2147483646
 * - i <= 2147483646
 * - 0 <= n
 * - n <= (2147483648 + h)
 * - (-1) <= i
 * - n <= (1 + h)
 * - (-1) <= j
 * - (-2147483648) <= x
 * - valid_rd(Malloc_0, a, 1)
 * - valid_rd(Malloc_0, shift_sint8(haystack_0, to_sint32(x)), 1)
 * - h <= (2147483647 + n)
 * - ((-1) <= brute_force_0) /\ ((brute_force_0 + n) <= h)
 * - !P_partial_match_at(Mchar_0, needle_0, haystack_0, i, n)
 * - P_partial_match_at(Mchar_0, needle_0, haystack_0, i, x_4)
 * - P_partial_match_at(Mchar_0, needle_0, haystack_0, i, 0)
 * - !P_match_at(Malloc_0, Mchar_0, needle_0, n, haystack_0, h, i)
 * - P_match_at(Malloc_0, Mchar_0, needle_0, n, haystack_0, h, brute_force_0)
 */
/*
 * Current invalid properties:
 */

#ifdef MAIN
int
main(int argc, char *argv[])
{
  printf("DEF in ABCDEFG: %d\n", brute_force("DEF", 3, "ABCDEFG", 7));
  printf("DEL in ABCDEFG: %d\n", brute_force("DEL", 3, "ABCDEFG", 7));
}
#endif

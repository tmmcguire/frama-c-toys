#include <string.h>

/*
 * Search for needile in haystack, using a brute force algorithm.
 *
 * Expected complexity is O(n*h), where n in the length of the needle and
 * h is the length of the haystack.
 */
int
brute_force (char *needle, int n, char *haystack, int h)
{
  int i, j;

  /* Searching */
  for (j = 0; j <= h - n; ++j) {
    for (i = 0; i < n && needle[i] == haystack[i + j]; ++i);
    if (i >= n) {
      return j;
    }
  }
  return -1;
}

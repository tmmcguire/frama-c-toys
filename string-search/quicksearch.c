#include <stdio.h>
#include <limits.h>

/*@
 @ // needle and bad_shift are valid arrays.
 @ requires \valid(needle + (0 .. n-1)) && 0 <= n < INT_MAX;
 @ requires \valid(bad_shift + (0 .. chars-1)) && 0 <= chars < INT_MAX;
 @ // needle and bad_shift are separate
 @ requires \separated(needle + (0 .. n-1), bad_shift + (0 .. chars-1));
 @ // the elements of needle are valid indices into bad_shift
 @ requires \forall int i; 0 <= i < n ==> 0 <= needle[i] < chars;
 @ // this function initializes bad_shift
 @ assigns *(bad_shift + (0 .. chars-1));
 @ // bad_shift is initialized to be between 1 and n+1
 @ ensures \forall int i; 0 <= i < chars ==> 1 <= bad_shift[i] <= n+1;
 */
void
make_bad_shift (unsigned char *needle, int n, int bad_shift[], int chars)
{
  int i;

  /*@
   @ loop assigns i, *(bad_shift + (0 .. chars-1));
   @ loop invariant 0 <= i <= chars;
   @ loop invariant \forall int k; 0 <= k < i ==> bad_shift[k] == n + 1;
   */
  for (i = 0; i < chars; ++i) {
    bad_shift[i] = n + 1;
  }
  /*@
   @ loop assigns i, *(bad_shift + (0 .. chars-1));
   @ loop invariant 0 <= i <= n;
   @ loop invariant \forall int k; 0 <= k < chars ==> 1 <= bad_shift[k] <= n+1;
   */
  for (i = 0; i < n; ++i) {
    bad_shift[needle[i]] = n - i;
  }
}

/*@
 @ // Original requirements for searching
 @ requires \valid(needle + (0 .. n-1)) && 0 <= n < INT_MAX;
 @ requires \valid(haystack + (0 .. h-1)) && 0 <= h < INT_MAX;
 @ requires n <= h;
 @ // the elements of needle are valid indices into bad_shift
 @ requires \forall int i; 0 <= i < n ==> 0 <= needle[i] < UCHAR_MAX + 1;
 @ assigns \nothing;
 */
int
QS (unsigned char *needle, int n, unsigned char *haystack, int h)
{
  int i, j, bad_shift[UCHAR_MAX + 1];

  /* Preprocessing */
  make_bad_shift(needle, n, bad_shift, UCHAR_MAX + 1);

  /* Searching */
  i = 0;
  /*@
   @ loop assigns i, j;
   @ loop invariant 0 <= i <= h + 1;
   */
  while (i <= h - n) {
    /*@
     @ loop assigns j;
     @ loop invariant 0 <= j <= n;
     */
    for (j = 0; j < n && needle[j] == haystack[i + j]; ++j);
    if (j >= n) {
      return i;
    }
    if (i == h - n) { break; }
    i += bad_shift[ haystack[i + n] ];	/* shift */
  }
  return -1;
}

#ifdef MAIN
int
main(int argc, char *argv[])
{
  printf("DEF in ABCDEFG: %d\n", QS("DEF", 3, "ABCDEFG", 7));
  printf("DEL in ABCDEFG: %d\n", QS("DEL", 3, "ABCDEFG", 7));
  printf("ABCB in XXXXXXXXX: %d\n", QS("ABCB", 4, "XXXXXXXXX", 9));
  printf("ABCB in XXXXXABCB: %d\n", QS("ABCB", 4, "XXXXXABCB", 9));
  printf("ABCB in XXXABCBXX: %d\n", QS("ABCB", 4, "XXXABCBXX", 9));
}
#endif

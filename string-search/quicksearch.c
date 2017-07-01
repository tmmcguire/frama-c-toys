#include <stdio.h>
#include <limits.h>

/*@
 @ // There is a partial match of length len, of the needle at location
 @ // loc in the haystack of length h. A complete match has length n.
 @ predicate match_at(int loc, unsigned char *haystack, int h,
 @                    unsigned char *needle, int len) =
 @   loc ≤ h - len
 @     ∧ ∀ int i; 0 ≤ i < len ⇒  needle[i] ≡ haystack[loc + i];
 */

/*@
 @ // needle and bad_shift are valid arrays.
 @ requires \valid(needle + (0 .. n-1)) ∧  0 ≤ n < INT_MAX;
 @ requires \valid(bad_shift + (0 .. chars-1)) ∧  0 ≤ chars < INT_MAX;
 @ // needle and bad_shift are separate
 @ requires \separated(needle + (0 .. n-1), bad_shift + (0 .. chars-1));
 @ // the elements of needle are valid indices into bad_shift
 @ requires ∀ int i; 0 ≤ i < n ⇒  0 ≤ needle[i] < chars;
 @ // this function initializes bad_shift
 @ assigns *(bad_shift + (0 .. chars-1));
 @ // safety: bad_shift has valid shifts
 @ ensures ∀ int c; 0 ≤ c < chars ⇒  1 ≤ bad_shift[c] ≤ n+1;
 @
 @ // progress: bad_shift has meaningful shifts
 @ ensures ∀ int c; 0 ≤ c < chars ⇒
 @   (∀ int k; n - bad_shift[c] + 1 ≤ k < n ⇒  needle[k] != c);
 */
void
make_bad_shift (unsigned char *needle, int n, int bad_shift[], int chars)
{
  int i;

  /*@
   @ loop assigns i, *(bad_shift + (0 .. chars-1));
   @ loop invariant 0 ≤ i ≤ chars;
   @ loop invariant ∀ int k; 0 ≤ k < i ⇒  bad_shift[k] == n + 1;
   */
  for (i = 0; i < chars; ++i) {
    bad_shift[i] = n + 1;
  }
  /*@
   @ loop assigns i, *(bad_shift + (0 .. chars-1));
   @ loop invariant 0 ≤ i ≤ n;
   @ loop invariant ∀ int c; 0 ≤ c < chars ⇒
   @   1 ≤ bad_shift[c] ≤ n + 1;
   @ loop invariant ∀ int c; 0 ≤ c < chars ⇒
   @   ∀ int k; n - bad_shift[c] + 1 ≤ k < i ⇒  needle[k] != c;
   */
  for (i = 0; i < n; ++i) {
    bad_shift[needle[i]] = n - i;
  }
}

/*@
 @ // Original requirements for searching
 @ requires \valid(needle + (0 .. n-1)) ∧  0 ≤ n < INT_MAX;
 @ requires \valid(haystack + (0 .. h-1)) ∧  0 ≤ h < INT_MAX;
 @ requires n ≤ h;
 @ // the elements of needle are valid indices into bad_shift
 @ requires ∀ int i; 0 ≤ i < n ⇒  0 ≤ needle[i] < UCHAR_MAX + 1;
 @ assigns \nothing;
 @ ensures -1 ≤ \result ≤ (h-n);
 @
 @ behavior success:
 @   ensures \result >= 0 ⇒  match_at(\result, haystack, h, needle, n);
 @ behavior failure:
 @   ensures \result == -1 ⇒
 @     ∀ int i; 0 ≤ i < h ⇒
 @       !match_at(i, haystack, h, needle, n);
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
   @ loop invariant 0 ≤ i ≤ h + 1;
   @ loop invariant ∀ int k; 0 ≤ k < i ⇒
   @   !match_at(k, haystack, h, needle, n);
   */
  while (i <= h - n) {
    /*@
     @ loop assigns j;
     @ loop invariant 0 ≤ j ≤ n;
     @ loop invariant match_at(i, haystack, h, needle, j);
     */
    for (j = 0; j < n && needle[j] == haystack[i + j]; ++j);
    if (j >= n) {
      return i;
    }
    if (i == h - n) { break; }

    /*@
     @ loop assigns j;
     @ loop invariant i + 1 ≤ j ≤ i + bad_shift[ haystack[i + n] ];
     @ loop invariant ∀ int k; i + 1 ≤ k < j ⇒
     @   !match_at(k, haystack, h, needle, n);
     */
    for (j = i + 1; j < i + bad_shift[ haystack[i + n] ]; ++j) {
      //@ assert haystack[i + n] != needle[i + n - j];
    }

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

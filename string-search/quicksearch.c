#include <stdio.h>
#include <limits.h>

/*@
 @ // There is a partial match of length len, of the needle at location
 @ // loc in the haystack of length h. A complete match has length n.
 @ predicate match_at(int loc, unsigned char *haystack, int h,
 @                    unsigned char *needle, int len) =
 @      loc ≤ h - len
 @   ∧  ∀ int k; 0 ≤ k < len ⇒  needle[k] ≡ haystack[loc + k];
 */

/*@
 @ // needle and bad_shift are valid arrays, are separate, and the
 @ // elements of needle are valid indices into bad_shift
 @ requires
 @      \valid(needle + (0 .. n-1))
 @   ∧  \valid(bad_shift + (0 .. chars-1))
 @   ∧  0 ≤ n < INT_MAX
 @   ∧  0 ≤ chars < INT_MAX
 @   ∧  \separated(needle + (0 .. n-1), bad_shift + (0 .. chars-1))
 @   ∧  ∀ int k; 0 ≤ k < n ⇒  0 ≤ needle[k] < chars;
 @
 @ // this function initializes bad_shift
 @ assigns
 @   *(bad_shift + (0 .. chars-1));
 @
 @ // safety: bad_shift has valid shifts
 @ // progress: bad_shift has meaningful shifts
 @ ensures
 @   ∀ int c; 0 ≤ c < chars ⇒ 
 @        (1 ≤ bad_shift[c] ≤ n+1
 @     ∧   ∀ int k; n - bad_shift[c] + 1 ≤ k < n ⇒  needle[k] != c);
 */
static void
make_bad_shift (unsigned char *needle, int n, int bad_shift[], int chars)
{
  int i;

  /*@
   @ loop assigns
   @   i, *(bad_shift + (0 .. chars-1));
   @ loop invariant
   @      0 ≤ i ≤ chars
   @   ∧  ∀ int k; 0 ≤ k < i ⇒  bad_shift[k] == n + 1;
   */
  for (i = 0; i < chars; ++i) {
    bad_shift[i] = n + 1;
  }
  /*@
   @ loop assigns
   @   i, *(bad_shift + (0 .. chars-1));
   @ loop invariant
   @      0 ≤ i ≤ n
   @   ∧  ∀ int c; 0 ≤ c < chars ⇒
   @        (1 ≤ bad_shift[c] ≤ n + 1
   @     ∧   ∀ int k; n - bad_shift[c] + 1 ≤ k < i ⇒  needle[k] != c);
   */
  for (i = 0; i < n; ++i) {
    bad_shift[needle[i]] = n - i;
  }
}

/*@
 @ // Original requirements for searching: valid strings;
 @ // also, the elements of needle are valid indices into bad_shift
 @ requires
 @      \valid(needle + (0 .. n-1))
 @   ∧  \valid(haystack + (0 .. h-1))
 @   ∧  0 ≤ n < INT_MAX
 @   ∧  0 ≤ h < INT_MAX
 @   ∧  n ≤ h
 @   ∧  ∀ int k; 0 ≤ k < n ⇒  0 ≤ needle[k] < UCHAR_MAX + 1;
 @
 @ // QS makes no globally visible changes
 @ assigns
 @   \nothing;
 @
 @ // safety: limits on return values
 @ ensures
 @   -1 ≤ \result ≤ (h-n);
 @
 @ // success: a match was found and the location returned
 @ behavior success:
 @   ensures
 @     \result >= 0 ⇒  match_at(\result, haystack, h, needle, n);
 @
 @ // failure: there is no match in the haystack
 @ behavior failure:
 @   ensures
 @     \result == -1 ⇒
 @       ∀ int k; 0 ≤ k < h ⇒
 @         !match_at(k, haystack, h, needle, n);
 */
int
QS (unsigned char *needle, int n, unsigned char *haystack, int h)
{
  int i, j, bad_shift[UCHAR_MAX + 1];
  //@ ghost int g;

  /* Preprocessing */
  make_bad_shift(needle, n, bad_shift, UCHAR_MAX + 1);
  /* Searching */
  i = 0;
  /*@
   @ loop assigns
   @   g, i, j;
   @ loop invariant
   @      0 ≤ i ≤ h + 1
   @   ∧  ∀ int k; 0 ≤ k < i ⇒
   @        !match_at(k, haystack, h, needle, n);
   */
  while (i <= h - n) {
    /*@
     @ loop assigns
     @   j;
     @ loop invariant
     @      0 ≤ j ≤ n
     @   ∧  match_at(i, haystack, h, needle, j);
     */
    for (j = 0; j < n && needle[j] == haystack[i + j]; ++j);
    if (j >= n) {
      return i;
    }
    if (i == h - n) { break; }

    /*@ ghost
     @  //@ loop assigns g; loop invariant i + 1 ≤ g ≤ i + bad_shift[ haystack[i + n] ]; loop invariant ∀ int k; i + 1 ≤ k < g ⇒  !match_at(k, haystack, h, needle, n);
     @  for (g = i + 1; g < i + bad_shift[ haystack[i + n] ]; ++g) {
     @    //@ assert haystack[i + n] != needle[i + n - g];
     @  }
     */

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

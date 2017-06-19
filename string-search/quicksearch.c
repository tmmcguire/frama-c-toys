#include <stdio.h>

#define ASIZE 256

void
make_bad_char_shift (char *needle, int n, int bad_char_shift[])
{
  int i;

  for (i = 0; i < ASIZE; ++i) {
    bad_char_shift[i] = n + 1;
  }
  for (i = 0; i < n; ++i) {
    bad_char_shift[needle[i]] = n - i;
  }
}

int
QS (char *needle, int n, char *haystack, int h)
{
  int i, j, bad_char_shift[ASIZE];

  /* Preprocessing */
  make_bad_char_shift (needle, n, bad_char_shift);

  /* Searching */
  i = 0;
  while (i <= h - n) {
    for (j = 0; j < n && needle[j] == haystack[i + j]; ++j);
    if (j >= n) {
      return i;
    }
    i += bad_char_shift[haystack[i + n]];	/* shift */
  }
  return -1;
}

#ifdef MAIN
int
main(int argc, char *argv[])
{
    printf("DEF in ABCDEFG: %d\n", QS("DEF", 3, "ABCDEFG", 7));
    printf("DEL in ABCDEFG: %d\n", QS("DEL", 3, "ABCDEFG", 7));
}
#endif

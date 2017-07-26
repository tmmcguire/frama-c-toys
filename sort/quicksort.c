#include <limits.h>
#include <stdio.h>

/*@
 @ predicate sorted(int *array, int l, int u) =
 @   ∀ int p, q; l ≤ p ≤ q < u ⇒  array[p] ≤ array[q];
 @*/

/*@
 @ predicate partitioned(int *array, int l, int m, int u) =
 @      (∀ int p; l ≤ p < m ⇒  array[p] ≤ array[m])
 @   ∧  (∀ int q; m < q < u ⇒  array[m] < array[q]);
 @*/

/*@
 @ predicate prsv_leq{L1,L2}(int *a, int l, int u, int v) =
 @   (∀ int p; l ≤ p < u ⇒  \at(a[p],L1) ≤ v) ⇒ 
 @     (∀ int p; l ≤ p < u ⇒  \at(a[p],L2) ≤ v);
 @*/

/*@
 @ predicate prsv_gt{L1,L2}(int *a, int l, int u, int v) =
 @   (∀ int p; l ≤ p < u ⇒  \at(a[p],L1) > v) ⇒ 
 @     (∀ int p; l ≤ p < u ⇒  \at(a[p],L2) > v);
 @*/

/*@
 @ axiomatic Permutation {
 @
 @   predicate permutation{L1,L2}(int *a, int l, int u)
 @     reads \at(a[l .. (u - 1)], L1), \at(a[l .. (u - 1)], L2);
 @
 @   axiom permute_refl{L}:
 @     ∀ int *a, l, u; permutation{L,L}(a,l,u);
 @
 @   axiom permute_unch{L1,L2}:
 @     ∀ int *a, l, u; ∀ int k; l ≤ k < u ⇒ 
 @       \at(a[k],L1) == \at(a[k],L2) ⇒  permutation{L1,L2}(a,l,u);
 @
 @   axiom permute_trans{L1,L2,L3}:
 @     ∀ int *a, l, u;
 @       permutation{L1,L2}(a,l,u) ⇒  permutation{L2,L3}(a,l,u) ⇒ 
 @         permutation{L1,L3}(a,l,u);
 @
 @   axiom permute_swap{L1,L2}:
 @     ∀ int *a, i, j, l, u;
 @       (\at(a[i],L1) == \at(a[j],L2)) ⇒ 
 @         (\at(a[j],L1) == \at(a[i],L2)) ⇒  
 @           (∀ int k; l ≤ k < u ∧  k != i ∧  k != j ⇒ 
 @             \at(a[k],L1) == \at(a[k],L2)) ⇒ 
 @               permutation{L1,L2}(a,l,u);
 @
 @ }
 @*/

/*@
 @ requires
 @      \valid(array + i)
 @   ∧  \valid(array + j);
 @ assigns
 @   array[i], array[j];
 @ ensures
 @      array[i] == \old(array[j])
 @   ∧  array[j] == \old(array[i]);
 @*/
void
swap(int *array, int i, int j)
{
  int tmp = array[i];
  array[i] = array[j];
  array[j] = tmp;
}

/*@
 @ requires
 @   0 ≤ l < l + 1 < u < INT_MAX;
 @ requires
 @   \valid(array + (l .. (u - 1)));
 @ assigns
 @   \nothing;
 @ ensures
 @   l ≤ \result < u;
 @*/
int
midpoint(int *array, int l, int u)
{
  return l + ((u - l) / 2);
}

/*@
 @ requires
 @   0 ≤ l < l + 1 < u < INT_MAX;
 @ requires
 @   \valid(array + (l .. (u - 1)));
 @ assigns
 @   *(array + (l .. (u - 1)));
 @ ensures
 @   l ≤ \result < u;
 @ ensures
 @   partitioned(array, l, \result, u);
 @ ensures
 @   ∀ int v; prsv_leq{Pre,Post}(array, l, u, v);
 @ ensures
 @   ∀ int v; prsv_gt{Pre,Post}(array, l, u, v);
 @ ensures
 @   permutation{Pre,Post}(array, l, u);
 @*/
int
partition(int *array, int l, int u)
{
  int i = l + 1;
  int j = u - 1;
  int m = midpoint(array, l, u);
  swap(array, l, m);
  /*@
   @ loop invariant
   @   l < i ≤ j < u;
   @ loop invariant
   @      (∀ int p; l < p < i ⇒  array[p] ≤ array[l])
   @   ∧  (∀ int q; j < q < u ⇒  array[l] < array[q]);
   @ loop assigns
   @   i, j, *(array + (l .. (u - 1)));
   @ loop invariant
   @   ∀ int v; prsv_leq{Pre,Here}(array, l, u, v);
   @ loop invariant
   @   ∀ int v; prsv_gt{Pre,Here}(array, l, u, v);
   @ loop invariant
   @   permutation{Pre,Here}(array, l, u);
   @*/
  while (i < j) {
    //@ ghost CurrentOuter:
    /*@
     @ loop invariant
     @   l + 1 ≤ i ≤ j < u;
     @ loop invariant
     @   ∀ int p; \at(i, CurrentOuter) ≤ p < i ⇒ 
     @     array[p] ≤ array[l];
     @ loop assigns
     @   i;
     @*/
    while (i < j && array[i] <= array[l]) {
      i += 1;
    }
    //@ assert ∀ int p; l < p < i ⇒  array[p] <= array[l];
    /*@
     @ loop invariant
     @   l + 1 ≤ i ≤ j < u;
     @ loop invariant
     @   ∀ int q; j < q ≤ \at(j, CurrentOuter) ⇒ 
     @     array[l] < array[q];
     @ loop assigns
     @   j;
     @*/
    while (i < j && array[l] < array[j]) {
      j -= 1;
    }
    //@ assert ∀ int q; j < q < u ⇒  array[l] < array[q];
    if (i < j) {
      //@ assert array[i] > array[l] >= array[j];
      swap(array, i, j);
      //@ assert array[i] <= array[l] < array[j];
    }
    //@ assert permutation{CurrentOuter,Here}(array, l, u);
  }
  //@ ghost PostLoop:
  if (array[l] < array[i]) {
    i -= 1;
  }
  swap(array, l, i);
  //@ assert permutation{PostLoop,Here}(array, l, u);
  return i;
}

/*@
 @ requires
 @   0 ≤ l ≤ u < INT_MAX;
 @ requires
 @   \valid(array + (l .. (u - 1)));
 @ assigns
 @   *(array + (l .. (u - 1)));
 @ ensures
 @   permutation{Pre,Post}(array, l, u);
 @ ensures
 @   ∀ int v; prsv_leq{Pre,Post}(array, l, u, v);
 @ ensures
 @   ∀ int v; prsv_gt{Pre,Post}(array, l, u, v);
 @ ensures
 @   sorted(array, l, u);
 @*/
void
qsort(int *array, int l, int u)
{
  if (u - l <= 1) {
    return;
  } else {
    int m = partition(array, l, u);
    //@ ghost PostPartition:
    qsort(array, l, m);
    //@ ghost int mm = m + 1;
    //@ assert ∀ int v; prsv_leq{Pre, Here}(array, l, u, v);
    //@ assert ∀ int v; prsv_gt{Pre, Here}(array, l, u, v);
    //@ assert prsv_gt{PostPartition, Here}(array, mm, u, array[m]);
    qsort(array, m + 1, u);
    //@ assert prsv_leq{PostPartition, Here}(array, l, m, array[m]);
    //@ assert prsv_gt{PostPartition, Here}(array, mm, u, array[m]);
  }
}

#ifdef MAIN

void
print_ary(char *name, int *array, int n)
{
  int i;
  printf("%s: ", name);
  for (i = 0; i < n; ++i) {
    printf(i > 0 ? ", %d" : "%d", array[i]);
  }
  printf("\n");
}

int
main(int argc, char *argv[])
{
  int a[] = { 0 };
  int asz = sizeof(a) / sizeof(int);
  int b[] = { 0, 3, 1 };
  int bsz = sizeof(b) / sizeof(int);
  int c[] = { 4, 3, 1, 0 };
  int csz = sizeof(c) / sizeof(int);
  int d[] = { 4, 3, 1, 0, 10, 82, 24, 21, 0, 3, 5, 2, 83, 99, 23, 1, 54 };
  int dsz = sizeof(d) / sizeof(int);
  print_ary("a", a, asz);
  qsort(a, 0, asz);
  print_ary("a", a, asz);

  print_ary("b", b, bsz);
  qsort(b, 0, bsz);
  print_ary("b", b, bsz);

  print_ary("c", c, csz);
  qsort(c, 0, csz);
  print_ary("c", c, csz);

  print_ary("d", d, dsz);
  qsort(d, 0, dsz);
  print_ary("d", d, dsz);

  return 0;
}

#endif /* MAIN */

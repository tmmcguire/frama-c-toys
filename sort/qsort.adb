with Ada.Text_IO;

package body QSort with SPARK_Mode is

   function Is_Partitioned
     (Ary : in Nat_Array;
      L   : Natural;
      P   : Natural;
      U   : Natural) return Boolean
   is
     ((for all K in L .. P => Ary(K) <= Ary(P))
      and then (for all K in P + 1 .. U => Ary(P) < Ary(K)))
   with
   Pre => (L in Ary'Range and then U in Ary'Range
           and then L <= P and then P <= U and then U < Natural'Last),
   Ghost;

--     procedure Lemma_LEq_Transitive
--       (A, B, C : in Nat_Array;
--        L, U : in Natural)
--       with
--         Ghost,
--         Pre => (A'First = B'First and then A'Last = B'Last
--                 and then A'First = C'First and then A'Last = C'Last
--                 and then L in A'Range and then U in A'Range
--                 and then L <= U and then U < Natural'Last
--                 and then (for all V in Natural'Range =>
--                             ((if LEq(A,L,U,V) then LEq(B,L,U,V))
--                              and then (if LEq(B,L,U,V) then LEq(C,L,U,V))))),
--       Post => (for all V in Natural'Range =>
--                  (if LEq(A,L,U,V) then LEq(C,L,U,V)))
--     is
--        MaxA : Natural;
--        I : Natural := L;
--     begin
--        MaxA := A(I);
--        while I <= U loop
--           pragma Loop_Invariant (L <= I and then I <= U);
--           pragma Loop_Invariant (for all K in L .. I - 1 => A(K) <= MaxA);
--           if MaxA < A(I) then
--              MaxA := A(I);
--           end if;
--           I := I + 1;
--        end loop;
--        pragma assert (LEq(A, L, U, MaxA));
--        pragma assert (LEq(B, L, U, MaxA));
--        pragma assert (LEq(C, L, U, MaxA));
--     end Lemma_LEq_Transitive;

   procedure Swap
     (Values   : in out Nat_Array;
      I        : in Natural;
      J        : in Natural;
      Original : in Nat_Array;
      Witness  : in out Nat_Array)
     with
       Pre  => (I in Values'Range and then J in Values'Range
                and then Is_Permutation(Values, Original, Witness)),
       Post => (Values(I) = Values'Old(J)
                and then Values(J) = Values'Old(I)
                and then (for all K in Values'Range =>
                            (K = I or else K = J
                             or else Values(K) = Values'Old(K)))
                and then Is_Permutation(Values, Original, Witness))
   is
      Temp : Natural;
   begin
      Temp       := Values(I);
      Values(I)  := Values(J);
      Values(J)  := Temp;
      Temp       := Witness(I);
      Witness(I) := Witness(J);
      Witness(J) := Temp;
   end Swap;

--     procedure Lemma_Swap_Preserve_LEq
--       (Pre, Post : in Nat_Array;
--        L, U : in Natural;
--        I, J : in Natural)
--       with
--         Ghost,
--         Pre => (Pre'First = Post'First and then Pre'Last = Post'Last
--                 and then L in Pre'Range and then U in Pre'Range
--                 and then L <= I and then I <= J and then J <= U
--                 and then Post(I) = Pre(J)
--                 and then Post(J) = Pre(I)
--                 and then (for all K in L .. U =>
--                             (K = I or else K = J
--                              or else Post(K) = Pre(K)))),
--       Post => (for all V in Natural'Range =>
--                  (if LEq(Pre,L,U,V) then LEq(Post,L,U,V)))
--     is
--     begin
--        null;
--     end Lemma_Swap_Preserve_LEq;

   procedure Midpoint
     (Values : in Nat_Array;
      L : in Natural;
      U : in Natural;
      M : out Natural)
     with
       Pre => (L in Values'Range and then U in Values'Range and then L <= U),
       Post => (L <= M and then M <= U)
   is
   begin
      M := L + ((U - L) / 2);
   end Midpoint;

   procedure Partition
     (Values   : in out Nat_Array;
      L        : in Natural;
      U        : in Natural;
      P        : out Natural;
      Original : in Nat_Array;
      Witness  : in out Nat_Array)
     with
       Pre  => (L in Values'Range and then U in Values'Range
                and then L < U and then U < Natural'Last
                and then Is_Permutation(Values, Original, Witness)),
       Post => (L <= P and then P <= U
                and then Is_Permutation(Values, Original, Witness)
                and then Is_Partitioned(Values, L, P, U)
                and then (for all V in Natural'Range =>
                            (if LEq(Values'Old, L, U, V)
                                 then LEq(Values, L, U, V))))
   is
      I       : Natural   := L;
      J       : Natural   := U;
      M       : Natural;
      Initial : Nat_Array := Values with Ghost;
   begin
      Midpoint(Values, L, U, M);
      Swap(Values, L, M, Original, Witness);

      while I < J loop
         pragma Loop_Invariant (L <= I and I <= J and J <= U);
         pragma Loop_Invariant (Is_Permutation(Values, Original, Witness));
         pragma Loop_Invariant (for all K in L .. I - 1 => Values(K) <= Values(L));
         pragma Loop_Invariant (for all K in J + 1 .. U => Values(L) < Values(K));
         pragma Loop_Invariant (for all V in Natural'Range =>
                                  (if LEq(Initial, L, U, V)
                                   then LEq(Values, L, U, V)));

         while I < J and then Values(I) <= Values(L) loop
            pragma Loop_Invariant (L <= I and I <= J and J <= U);
            pragma Loop_Invariant (for all K in L .. I => Values(K) <= Values(L));
            I := I + 1;
         end loop;
         pragma assert (for all K in L .. I - 1 => Values(K) <= Values(L));

         while I < J and then Values(L) < Values(J) loop
            pragma Loop_Invariant (L <= I and I <= J and J <= U);
            pragma Loop_Invariant (for all K in J .. U => Values(L) < Values(K));
            J := J - 1;
         end loop;
         pragma assert (for all K in J + 1 .. U => Values(L) < Values(K));

         if I < J then
            pragma assert (Values(I) > Values(L) and Values(L) >= Values(J));
            Swap(Values, I, J, Original, Witness);
            pragma assert (Values(I) <= Values(L) and then Values(L) < Values(J));
         end if;
      end loop;

      pragma assert (I = J);
      if Values(I) > Values(L) then
         I := I - 1;
      end if;
      pragma assert (L <= I);

      Swap(Values, L, I, Original, Witness);

      pragma assert (for all K in L .. I => Values(K) <= Values(I));
      pragma assert (for all K in I + 1 .. U => Values(I) < Values(K));

      pragma assert (for all V in Natural'Range => (if LEq(Initial, L, U, V)
                                                    then LEq(Values, L, U, V)));

      P := I;
   end Partition;

   ------------------------------------

   procedure Sort
     (Values   : in out Nat_Array;
      L        : in Natural;
      U        : in Natural;
      Original : in Nat_Array;
      Witness  : in out Nat_Array)
   is
      P : Natural;
   begin
      if U - L < 1 then
         return;
      else
         Partition(Values, L, U, P, Original, Witness);
         if P - L > 1 then
            Sort(Values, L, P - 1, Original, Witness);
         end if;
         if U - P > 1 then
            Sort(Values, P + 1, U, Original, Witness);
         end if;
      end if;
   end Sort;


end QSort;

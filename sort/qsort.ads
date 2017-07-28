package QSort with SPARK_Mode is

   type Nat_Array is array (Natural range <>) of Natural;

   function Is_Permutation
     (Ary : in Nat_Array;
      Original : in Nat_Array;
      Witness : in Nat_Array) return Boolean
   is
      (Ary'First = Original'First and then Ary'Last = Original'Last
       and then Ary'First = Witness'First and then Ary'Last = Witness'Last
       and then (for all K in Witness'Range => Witness(K) in Original'Range)
       and then (for all K in Ary'Range => Ary(K) = Original( Witness(K) )))
   with Ghost;

   function Is_Sorted(Ary : in Nat_Array) return Boolean
   is
     (for all P in Ary'Range =>
        (for all Q in P .. Ary'Last =>
              Ary(P) <= Ary(Q)))
   with Ghost;

   procedure Sort
     (Values : in out Nat_Array;
      L : in Natural;
      U : in Natural;
      Original : in Nat_Array;
      Witness : in out Nat_Array)
     with
       Pre => (L in Values'Range and then U in Values'Range
               and then U < Natural'Last
               and then Is_Permutation(Values, Original, Witness)),
       Post => (Is_Permutation(Values, Original, Witness));

end QSort;

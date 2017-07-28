with Ada.Text_IO;
use Ada.Text_IO;

with QSort;

procedure Main is

   package NIO is new Ada.Text_IO.Integer_IO (Natural);

   procedure Print_Array(A : QSort.Nat_Array) is
   begin
      for I in A'Range loop
         NIO.Put(Item  => A(I),
                 Width => 4);
      end loop;
      New_Line;
   end Print_Array;

   procedure Initialize_Witness(A : out QSort.Nat_Array) is
   begin
      for I in A'Range loop
         A(I) := I;
      end loop;
   end Initialize_Witness;

   A : QSort.Nat_Array := (0 => 0);
   B : QSort.Nat_Array := (0, 3, 1);
   C : QSort.Nat_Array := (4, 3, 1, 0);
   D : QSort.Nat_Array := (4, 3, 1, 0, 10, 82, 24, 21, 0, 3, 5, 2, 83, 99, 23, 1, 54);

   AO : QSort.Nat_Array := A;
   BO : QSort.Nat_Array := B;
   CO : QSort.Nat_Array := C;
   EO : QSort.Nat_Array := D;

   AW : QSort.Nat_Array := A;
   BW : QSort.Nat_Array := B;
   CW : QSort.Nat_Array := C;
   DW : QSort.Nat_Array := D;

begin
   Initialize_Witness(AW);
   Initialize_Witness(BW);
   Initialize_Witness(CW);
   Initialize_Witness(DW);

   Print_Array(A);
   QSort.Sort(A, A'First, A'Last, AO, AW);
   Print_Array(A);

   Print_Array(B);
   QSort.Sort(B, B'First, B'Last, BO, BW);
   Print_Array(B);

   Print_Array(C);
   QSort.Sort(C, C'First, C'Last, CO, CW);
   Print_Array(C);

   Print_Array(D);
   QSort.Sort(D, D'First, D'Last, EO, DW);
   Print_Array(D);
end Main;


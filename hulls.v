Require Import Bool Arith List Psatz Coq.Unicode.Utf8.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.Orders.
Require Import MSetAVL.

Module N2 := PairOrderedType Nat_as_OT Nat_as_OT.
Module Triangle := PairOrderedType Nat_as_OT N2.
Module TriangleSet := MSetAVL.Make Triangle.

Notation "[ x , y , z ]" := (x,(y,z)).

Definition insert csq_orig t csq_new :=
  if TriangleSet.mem t csq_orig then
    csq_new
  else
    TriangleSet.add t csq_new.

Definition step1 csq_orig t csq_new :=
  match t with
      [a,b,c] =>
      insert csq_orig [b,c,a] csq_new
  end.

Definition step4_aux csq_orig a b d t csq_new :=
  match t with
      [b',c,d'] =>
      if N2.eq_dec (b,d) (b',d') then
        if TriangleSet.mem [c,a,d] csq_orig then
          insert csq_orig [a,b,c] csq_new
        else
          csq_new
      else
        csq_new
  end.

Definition step4 csq_orig t csq_new :=
  match t with
      [a,b,d] =>
      TriangleSet.fold (step4_aux csq_orig a b d) csq_orig csq_new
  end.

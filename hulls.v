Require Import Bool Arith List Psatz Coq.Unicode.Utf8.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.Orders.
Require Import MSetAVL.

Module N2 := PairOrderedType Nat_as_OT Nat_as_OT.
Module Triangle := PairOrderedType Nat_as_OT N2.
Module TriangleSet := MSetAVL.Make Triangle.

Notation "[ x , y , z ]" := (x,(y,z)).
Notation "{{ x , .. , y }}" := (TriangleSet.add x .. (TriangleSet.add y TriangleSet.empty) .. ).
Notation "{{}}" := TriangleSet.empty.

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

Definition step5_aux_aux csq_orig a b c d t csq_new :=
  match t with
      [a',b',e] =>
      if N2.eq_dec (a, b) (a' ,b') then
        if TriangleSet.mem [a,c,d] csq_orig && TriangleSet.mem [a,d,e] csq_orig then
          insert csq_orig [a,c,e] csq_new
        else
          csq_new
      else
        csq_new
  end.

Definition step5_aux csq_orig a b c t csq_new :=
  match t with
      [a',b',d] =>
      if N2.eq_dec (a, b) (a' ,b') then
        TriangleSet.fold (step5_aux_aux csq_orig a b c d) csq_orig csq_new
      else
        csq_new
  end.

Definition step5 csq_orig t csq_new :=
  match t with
      [a,b,d] =>
      TriangleSet.fold (step5_aux csq_orig a b d) csq_orig csq_new
  end.

(*** Tests step1, step4, step5  ***)
Definition t231 := [2,3,1].
Definition t243 := [2,4,3].
Definition t413 := [4,1,3].
Definition t253 := [2,5,3].
Definition t513 := [5,1,3].
Definition t125 := [1,2,5].

Definition test5 := {{[1,2,3],[1,2,4],[1,2,5],[1,3,4],[1,4,5]}}.
Compute (TriangleSet.elements (step5 test5 [1,2,3] {{}})).

Definition set1 := TriangleSet.add t123 TriangleSet.empty.
Definition set1' := TriangleSet.add t231 set1.
Definition set2 := TriangleSet.add t243 set1.
Definition set3 := TriangleSet.add t413 set2.
Definition set4 := TriangleSet.add t253 set3.
Definition set5 := TriangleSet.add t513 set4.
Definition set5' := TriangleSet.add t125 set5.

Compute (step1 set1 t123 TriangleSet.empty).
Compute (step1 set1' t123 TriangleSet.empty).
Compute (step1 set3 t123 TriangleSet.empty).

Compute (step4 set3 t123 TriangleSet.empty).
Compute (step4 set5 t123 TriangleSet.empty).
Compute (step4 set5' t123 TriangleSet.empty).

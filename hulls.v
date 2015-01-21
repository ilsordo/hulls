Require Import Bool Arith List Psatz Coq.Unicode.Utf8.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.Structures.Orders.
Require Import MSetAVL.

Module N2 := PairOrderedType Nat_as_OT Nat_as_OT.
Module Triangle := PairOrderedType Nat_as_OT N2.
Module TS := MSetAVL.Make Triangle.

Notation "[ x , y , z ]" := (x,(y,z)).
Notation "{{ x , .. , y }}" := (TS.add x .. (TS.add y TS.empty) .. ).
Notation "{{}}" := TS.empty.

Definition insert csq_orig t csq_new :=
  if TS.mem t csq_orig then
    csq_new
  else
    TS.add t csq_new.

Definition step1 csq_orig t csq_new :=
  match t with
      [a,b,c] =>
      insert csq_orig [b,c,a] csq_new
  end.

Definition step4_aux csq_orig a b d t csq_new :=
  match t with
      [b',c,d'] =>
      if N2.eq_dec (b,d) (b',d') then
        if TS.mem [c,a,d] csq_orig then
          insert csq_orig [a,b,c] csq_new
        else
          csq_new
      else
        csq_new
  end.

Definition step4 csq_orig t csq_new :=
  match t with
      [a,b,d] =>
      TS.fold (step4_aux csq_orig a b d) csq_orig csq_new
  end.

Definition step5_aux_aux csq_orig a b c d t csq_new :=
  match t with
      [a',b',e] =>
      if N2.eq_dec (a, b) (a' ,b') then
        if TS.mem [a,c,d] csq_orig && TS.mem [a,d,e] csq_orig then
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
        TS.fold (step5_aux_aux csq_orig a b c d) csq_orig csq_new
      else
        csq_new
  end.

Definition step5 csq_orig t csq_new :=
  match t with
      [a,b,d] =>
      TS.fold (step5_aux csq_orig a b d) csq_orig csq_new
  end.

(*** Tests step1, step4, step5  ***)
(*****
Definition test1 := {{[1,2,3],[2,3,4]}}.
Compute (TS.elements (step1 test1 [1,2,3] {{}})).

Definition test1' := {{[1,2,3],[2,3,1]}}.
Compute (TS.elements (step1 test1' [1,2,3] {{}})).

Definition test4 := {{[1,2,3],[2,4,3],[4,1,3]}}.
Compute (TS.elements (step4 test4 [1,2,3] {{}})).

Definition test5 := {{[1,2,3],[1,2,4],[1,2,5],[1,3,4],[1,4,5]}}.
Compute (TS.elements (step5 test5 [1,2,3] {{}})).
*****)

Definition step145 csq_orig :=
  let csq_new := TS.fold (step1 csq_orig) csq_orig TS.empty in
  let csq_new' := TS.fold (step4 csq_orig) csq_orig csq_new in
  let csq_new'' := TS.fold (step5 csq_orig) csq_orig csq_new' in
  if TS.is_empty csq_new then
    inl csq_orig
  else
    inr (TS.union csq_orig csq_new).

Definition csq_proj (r : TS.t + TS.t) := match r with
                           | inl csq => csq
                           | inr csq => csq
                         end.

Fixpoint sat145 csq fuel {struct fuel} :=
  match fuel with
    | O => csq
    | S p =>
      match step145 csq with
        | inl csq' => csq'
        | inr csq' => sat145 csq' p
      end
  end.

Inductive Conseq : TS.t -> Triangle.t -> Prop :=
  | Id : forall ts t, TS.In t ts -> Conseq ts t
  | Rule1 : forall ts a b c, TS.In [a,b,c] ts -> Conseq ts [b,c,a]
  | Rule4 : forall ts a b c d, TS.In [a,b,d] ts -> TS.In [b,c,d] ts -> TS.In [c,a,d] ts -> Conseq ts [a,b,c]
  | Rule5 : forall ts a b c d e, TS.In [a,b,c] ts -> TS.In [a,b,d] ts -> TS.In [a,b,e] ts -> TS.In [a,c,d] ts -> TS.In [a,d,e] ts -> Conseq ts [a,c,e].

Inductive Conseqs : TS.t -> TS.t -> Prop :=
  | Conseq_add : forall ts ts', (forall t, (TS.In t ts') -> Conseq ts t) -> Conseqs ts ts'
  | Conseq_trans : forall ts ts' ts'', Conseqs ts ts' -> Conseqs ts' ts'' -> Conseqs ts ts''.

Definition step_correct step := forall csq_orig csq_new (t : Triangle.t), Conseqs csq_orig csq_new -> Conseqs csq_orig (step csq_orig t csq_new).

Lemma fold_step_correct :
  forall csq_orig csq_new step,
    Conseqs csq_orig csq_new ->
    step_correct step ->
    Conseqs csq_orig (TS.fold (step csq_orig) csq_orig csq_new).
Proof.

Admitted.

Lemma step145_correct : forall ts t, Conseqs ts (csq_proj (step145 ts))
Proof.

Admitted.

Theorem sat145_correct : forall ts fuel, Conseqs ts (sat145 ts fuel).
Proof.

Admitted.


Definition inconsistent csq :=
  TS.exists_ (fun t => match t with [a,b,c] => TS.mem [a,c,b] csq end).

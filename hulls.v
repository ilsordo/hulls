Require Import Bool Arith List Psatz Coq.Unicode.Utf8.
Require Import Structures.OrdersEx.
Require Import Structures.Orders.
Require Import MSetAVL.

Require MSets.MSetFacts.
Require Coq.MSets.MSetProperties.

Module N2 := PairOrderedType Nat_as_OT Nat_as_OT.
Module Triangle := PairOrderedType Nat_as_OT N2.
Module TS := MSetAVL.Make Triangle.

Module TS_Facts := MSetFacts.Facts TS.
Module SetProps := MSetProperties.Properties(TS).

Lemma eq_is_eq : forall x y, Triangle.eq x y -> x = y.
Proof.
  intros [x1 [x2 x3]] [y1 [y2 y3]] H.
  compute in *.
  intuition.
  subst.
  auto.
Qed.

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

Definition step4_aux a b d csq_orig t csq_new :=
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
      TS.fold (step4_aux a b d csq_orig) csq_orig csq_new
  end.

Definition step5_aux_aux a b c d csq_orig t csq_new :=
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

Definition step5_aux a b c csq_orig t csq_new :=
  match t with
      [a',b',d] =>
      if N2.eq_dec (a, b) (a' ,b') then
        TS.fold (step5_aux_aux a b c d csq_orig) csq_orig csq_new
      else
        csq_new
  end.

Definition step5 csq_orig t csq_new :=
  match t with
      [a,b,d] =>
      TS.fold (step5_aux a b d csq_orig) csq_orig csq_new
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

Definition step_correct step := forall csq_orig csq_new (t : Triangle.t), TS.In t csq_orig -> Conseqs csq_orig csq_new -> Conseqs csq_orig (step csq_orig t csq_new).

Hint Constructors Conseq Conseqs.

Require Coq.MSets.MSetFacts.
Module SetFacts := MSetFacts.WFacts(TS).

Lemma step1_correct : step_correct step1.
Proof.
  unfold step_correct.
  intros.
  destruct t; destruct p.
  simpl.
  apply Conseq_add.
  intros.
  destruct t; destruct p.
  unfold insert in H1.
  destruct (Triangle.eq_dec [n0,n1,n] [n2,n3,n4]).
  - apply eq_is_eq in e.
    rewrite <- e in *.
    apply Rule1; auto.
  - simpl H1.
    apply Id.
    assert (TS.In [n2, n3, n4] csq_new).
    + destruct (TS.mem [n0, n1, n] csq_orig); auto.
      apply (SetFacts.add_neq_iff csq_new) in n5.
      intuition.
    +
Admitted.

Lemma step5_aux_aux_correct :
  forall a b c d csq_orig csq_new t,
    TS.In [a,b,c] csq_orig ->
    TS.In [a,b,d] csq_orig ->
    TS.In t csq_orig ->
    (forall t, TS.In t csq_new -> Conseq csq_orig t) ->
    Conseqs csq_orig (step5_aux_aux a b c d csq_orig t csq_new).
Proof.
  intros a b c d csq_orig csq_new (a',(b',e)) Habc Habd Ht Hacc.
  unfold step5_aux_aux.
  destruct (N2.eq_dec (a, b) (a', b')); [ |constructor; exact Hacc].
  compute in e0.
  destruct e0 as [ea eb].
  symmetry in ea,eb. subst.
  case_eq (TS.mem [a, c, d] csq_orig && TS.mem [a, d, e] csq_orig); [ |intros; constructor; exact Hacc].
  intro eq.
  unfold insert.
  case_eq (TS.mem [a, c, e] csq_orig); [intros; constructor; exact Hacc |].
  intro Hace.
  apply Conseq_add.
  intros (x,(y,z)) Ht'.
  destruct (Triangle.eq_dec [x, y, z] [a, c, e]).
  + compute in e0. destruct e0 as [ea e0]. destruct e0 as [ec ee]. subst.
    apply andb_prop in eq. destruct eq as [Hmem1 Hmem2].
    apply TS_Facts.mem_2 in Hmem1. apply TS_Facts.mem_2 in Hmem2.
    apply (Rule5 csq_orig a b c d e); try assumption.
  + apply Hacc. apply TS_Facts.add_3 with (x := [a, c, e]).
    * compute. compute in n. intuition.
    * exact Ht'.
Qed.

Lemma step5_correct : step_correct step5.
Proof.
  unfold step_correct, step5.
  intros csq_orig csq_new (a,(b,c)) T_in_csq Hrec.
  constructor.
  intros (a',(b',c')).
  intro.

Lemma conseq_congr: forall s1 s2 k (EQ: TS.Equal s1 s2),
    Conseq s1 k -> Conseq s2 k.
Proof.
  intros. unfold TS.Equal in EQ. induction H; firstorder. 
  + constructor 3 with d; firstorder.
  + constructor 4 with b d; firstorder.
Qed.    

Lemma conseqs_congr: forall s1 s2 k (EQ: TS.Equal s1 s2),
    Conseqs s1 k -> Conseqs s2 k.
Proof.
  intros.
  induction H.
  + econstructor 1. eauto using conseq_congr.
  + econstructor 2; eauto. 
Qed.  


Lemma fold_step_correct :
  forall csq_new csq_orig step,
    Conseqs csq_orig csq_new ->
    step_correct step ->
    Conseqs csq_orig (TS.fold (step csq_orig) csq_orig csq_new).
Proof.
  Hint Resolve conseq_congr conseqs_congr.
  intros; eapply SetProps.fold_rec_nodep; intros; eauto.
Qed.

Admitted.

Lemma step145_correct : forall ts t, Conseqs ts (csq_proj (step145 ts)).
Proof.

Admitted.

Theorem sat145_correct : forall ts fuel, Conseqs ts (sat145 ts fuel).
Proof.

Admitted.


Definition inconsistent csq :=
  TS.exists_ (fun t => match t with [a,b,c] => TS.mem [a,c,b] csq end).

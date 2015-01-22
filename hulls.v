Require Import Bool Arith List Psatz Coq.Unicode.Utf8.
Require Import Structures.OrdersEx.
Require Import Structures.Orders.
Require Import MSetAVL.

Require Import DLib.

Require MSets.MSetFacts.
Require Coq.MSets.MSetProperties.

Module N2 := PairOrderedType Nat_as_OT Nat_as_OT.
Module Triangle := PairOrderedType Nat_as_OT N2.
Module TS := MSetAVL.Make Triangle.

Module SetFacts := MSetFacts.Facts TS.
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
  (* abd /\ bcd /\ cad -> abc *)
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
  if TS.is_empty csq_new'' then
    inl csq_orig
  else
    inr (TS.union csq_orig csq_new'').

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

Definition Conseqs_imm ts ts' := (forall t, (TS.In t ts') -> Conseq ts t).

Definition step_correct step := forall csq_orig csq_new (t : Triangle.t),
    TS.In t csq_orig ->
    Conseqs_imm csq_orig csq_new ->
    Conseqs_imm csq_orig (step csq_orig t csq_new).

Hint Constructors Conseq.
Hint Unfold Conseqs_imm.

Lemma step1_correct : step_correct step1.
Proof.
  unfold step_correct.
  intros.
  destruct t; destruct p.
  simpl.
  unfold Conseqs_imm.
  intros.
  destruct t; destruct p.
  unfold insert in H1.
  destruct (Triangle.eq_dec [n0,n1,n] [n2,n3,n4]).
  - apply eq_is_eq in e.
    rewrite <- e in *.
    apply Rule1; auto.
  - assert (TS.In [n2, n3, n4] csq_new).
    + destruct (TS.mem [n0, n1, n] csq_orig); auto.
      apply (SetFacts.add_neq_iff csq_new) in n5.
      intuition.
    + apply H0; auto.
Qed.

Lemma step4_aux_correct :
  forall a b c csq_orig t csq_new,
    TS.In [a,b,c] csq_orig ->
    TS.In t csq_orig ->
    Conseqs_imm csq_orig csq_new ->
    Conseqs_imm csq_orig (step4_aux a b c csq_orig t csq_new).
Proof.
  intros.
  destruct t; destruct p.
  unfold step4_aux.
  unfold Conseqs_imm.
  intros.
  destruct (N2.eq_dec (b, c) (n, n1)).
  - case_eq (TS.mem [n0, a, c] csq_orig).
    + intros.
      rewrite H3 in H2.
      unfold insert in H2.
      case_eq (TS.mem [a, b, n0] csq_orig); intro.
      * rewrite H4 in *; auto.
      * rewrite H4 in *.
        unfold Conseqs_imm in H1.
        destruct t; destruct p.
        compute in e; intuition; subst.
        destruct (Triangle.eq_dec [a,n,n0] [n2,n3,n4]).
        { compute in e.
          intuition; subst.
          apply (Rule4 csq_orig n2 n3 n4 n1); repeat (intuition).
        }
        apply (SetFacts.add_neq_iff csq_new) in n5.
        intuition.
    + intros.
      rewrite H3 in H2.
      intuition.
  - intuition.
Qed.

Lemma step4_correct : step_correct step4.
Proof.
  unfold step_correct.
  intros csq_orig csq_new (a, (b, c)).
  unfold step4.
  intros.
  eapply SetProps.fold_rec_nodep.
  + auto.
  + intros.
    eapply step4_aux_correct; eauto.
Qed.

Lemma step5_aux_aux_correct :
  forall a b c d csq_orig csq_new t,
    TS.In [a,b,c] csq_orig ->
    TS.In [a,b,d] csq_orig ->
    TS.In t csq_orig ->
    Conseqs_imm csq_orig csq_new ->
    Conseqs_imm csq_orig (step5_aux_aux a b c d csq_orig t csq_new).
Proof.
  intros a b c d csq_orig csq_new (a',(b',e)) Habc Habd Ht Hacc.
  unfold step5_aux_aux.
  flatten; auto.
  compute in e0.
  destruct e0 as [ea eb].
  symmetry in ea,eb. subst.
  unfold insert.
  flatten; auto.
  unfold Conseqs_imm.
  intros (x,(y,z)) Ht'.
  destruct (Triangle.eq_dec [x, y, z] [a, c, e]).
  + compute in e0. destruct e0 as [ea e0]. destruct e0 as [ec ee]. subst.
    apply andb_prop in Eq. destruct Eq as [Hmem1 Hmem2].
    apply SetFacts.mem_2 in Hmem1. apply SetFacts.mem_2 in Hmem2.
    apply (Rule5 csq_orig a b c d e); try assumption.
  + apply Hacc. apply SetFacts.add_3 with (x := [a, c, e]).
    * compute. compute in n. intuition.
    * exact Ht'.
Qed.


Lemma step5_aux_correct :
  forall a b c csq_orig csq_new t,
    TS.In [a,b,c] csq_orig ->
    TS.In t csq_orig ->
    Conseqs_imm csq_orig csq_new ->
    Conseqs_imm csq_orig (step5_aux a b c csq_orig t csq_new).
Proof.
  intros a b c csq_orig csq_new (a',(b',e)) Habc Ht Hacc.
  unfold step5_aux.
  flatten; auto.
  eapply SetProps.fold_rec_nodep; eauto.
  intros.
  compute in e0. destruct e0 as [ea eb]. subst.
  apply step5_aux_aux_correct; auto.
Qed.

Lemma step5_correct : step_correct step5.
Proof.
  unfold step_correct, step5.
  intros csq_orig csq_new (a,(b,c)) T_in_csq Hrec.
  eapply SetProps.fold_rec_nodep; eauto.
  intros. apply step5_aux_correct; auto.
Qed.

Lemma fold_step_correct :
  forall csq_new csq_orig step,
    Conseqs_imm csq_orig csq_new ->
    step_correct step ->
    Conseqs_imm csq_orig (TS.fold (step csq_orig) csq_orig csq_new).
Proof.
  intros; eapply SetProps.fold_rec_nodep; intros; eauto.
Qed.

Lemma union_csq_imm: forall old new,
  Conseqs_imm old new -> Conseqs_imm old (TS.union old new).
Proof.
  intros old new H x Hincl.
  apply TS.union_spec in Hincl.
  destruct Hincl; eauto.
Qed.


Lemma step145_correct : forall ts, Conseqs_imm ts (csq_proj (step145 ts)).
Proof.
  Hint Resolve step1_correct step4_correct step5_correct fold_step_correct.
  intros orig. destruct (step145 orig) eqn:eq.
  + intro. simpl in *. unfold step145 in eq. flatten eq.
    apply TS.is_empty_spec in Eq. apply SetProps.empty_is_empty_1 in Eq. eauto.
  + simpl in *. unfold step145 in *. flatten eq.
    match goal with
    | [ |- Conseqs_imm orig (TS.union orig ?x)] =>
      assert (Conseqs_imm orig x)
    end.
    { repeat (eapply fold_step_correct); eauto. intro. intro. constructor 1. apply TS.empty_spec in H.
      contradiction. }
    eauto using union_csq_imm.
Qed.

Inductive Conseqs : TS.t -> TS.t -> Prop :=
  | Imm : forall ts ts', Conseqs_imm ts ts' -> Conseqs ts ts'
  | Trans : forall ts ts' ts'', Conseqs_imm ts ts' -> Conseqs ts' ts'' -> Conseqs ts ts''.

Hint Constructors Conseqs.

Lemma step145_effective_correct : forall ts csq, inr csq = step145 ts -> Conseqs_imm ts csq.
Proof.
  Hint Resolve step145_correct.
  intros. replace csq with (csq_proj (inr csq)) by auto.
  rewrite H. auto.
Qed.

Theorem sat145_correct : forall fuel ts, Conseqs ts (sat145 ts fuel).
Proof.
  induction fuel; simpl; auto.
  intro. flatten. unfold step145 in Eq; flatten Eq; auto.
  eapply Trans; [| eauto].
  eapply step145_effective_correct; auto.
Qed.


Definition inconsistent csq :=
  TS.exists_ (fun t => match t with [a,b,c] => TS.mem [a,c,b] csq end) csq.

Check inconsistent.

Fixpoint refute' (worklist : list Triangle.t) (problem : TS.t) :=
  match worklist with
      | nil => false
      | [m,n,p]::wl =>
        if inconsistent problem then true
        else if negb (refute' wl (sat145 (TS.add [m,n,p] problem) 1000))
             then false
             else refute' wl (sat145 (TS.add [m,p,n] problem) 1000)
  end.

Fixpoint enumerate len n : list (list nat) :=
  match n with
      O => match len with
               | O => nil::nil
               | S p => nil
           end
    | S p =>
      match len with
        | O => nil::nil
        | S l =>
          List.map (fun e => 1::List.map (fun x => x + 1) e)
                   (enumerate l p)++
                   List.map (fun e => List.map (fun x => x + 1) e)
                   (enumerate (S l) p)
      end
  end.

Definition triplets_to_triangles :=
  List.map (
      fun triplet => match triplet with
                       | a::b::c::nil => [a,b,c]
                       | _ => [1,1,1]
                     end
    )
.

(* 123 234 152 253 354 145 :
             5
            /|
           / |
          2--3
         /   |
        /    |
       1     4 
*)
Definition canonical_problem := {{[1,2,3], [2,3,4], [1,5,2], [2,5,3], [1,4,5]}}.
Definition refute l := refute' (triplets_to_triangles (enumerate 3 5)) (sat145 l 1000).

Notation "x ∈ y" := (TS.In x y ) (at level 10).

Section FINAL.
  Parameter A : Type.
  Parameter oriented : A -> A -> A -> Prop.
  Parameter inj : nat -> A.
  Parameter inj_inj : ∀ x y, inj x = inj y -> x = y.
  Definition δ t := match t with [x, y, z] => oriented (inj x) (inj y) (inj z) end.
  Definition Δ := TS.For_all δ.
  Parameter rule1 : forall a b c, δ [a, b, c] -> δ [b, c, a].
  Parameter rule2 : forall a b c, a ≠ b -> b ≠ c -> c ≠ a -> δ [a, b, c] -> ¬δ [c, b, a].
  Parameter rule3 : forall a b c, δ [a, b, c] ∨ δ [c, b, a].
  Parameter rule4 : forall a b c d, δ [a, b, d] -> δ [b, c, d] -> δ [c, a, d] -> δ [a, b, c].
  Parameter rule5 : forall a b c d e, δ [a, b, c] -> δ [a, b, d] -> δ [a, b, e] -> δ [a, c, d] -> δ [a, d, e] -> δ [a, c, e].
  Parameter hyps : TS.t.
  Hypothesis hyps_spec : Δ hyps.
  Parameter ziel : Triangle.t.

  Lemma Conseqs_spec : forall ts ts', Conseqs ts ts' -> Δ ts -> Δ ts'.
  Admitted.

  Lemma sat145_spec : forall ts fuel, Δ ts -> Δ (sat145 ts fuel).
  Admitted.

  Lemma inconsistent_spec : forall ts, Δ ts -> inconsistent ts = true -> False.
  Admitted.

  Lemma refute_spec : forall ts, Δ ts -> refute ts = true -> False.
  Admitted.

  Hypothesis refute_true : refute (TS.add ziel hyps) = true.

  Theorem cool : False.
  Proof.
  Admitted.

End FINAL.

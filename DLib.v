(* © David Pichardie <david.pichardie@inria.fr> *)

Ltac autoinjection :=
  repeat match goal with
           | h: ?f _ = ?f _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ = ?f _  _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ = ?f _ _ _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ _ = ?f _ _ _ _ |- _ => injection h; intros; clear h; subst
           | h: ?f _ _ _ _ _ = ?f _ |- _ _ _ _ _ => injection h; intros; clear h; subst
         end.

(* Détruit tous les matchs récursivement *)
Tactic Notation "flatten" ident(H) :=
  repeat match goal with
    | H: context[match ?x with | left _ => _ | right _ => _ end] |- _ => destruct x
    | H: context[match ?x with | _ => _ end] |- _ => let E := fresh "Eq" in destruct x eqn:E
  end; autoinjection; try congruence.

Tactic Notation "flatten" :=
  repeat match goal with
    | |- context[match ?x with | left _ => _ | right _ => _ end] => destruct x
    | |- context[match ?x with | _ => _ end] => let E := fresh "Eq" in destruct x eqn:E
  end; autoinjection; try congruence.

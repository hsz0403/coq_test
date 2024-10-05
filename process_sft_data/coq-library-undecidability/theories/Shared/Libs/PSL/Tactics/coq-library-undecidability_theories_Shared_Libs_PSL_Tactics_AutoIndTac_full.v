Ltac revert_all := repeat match goal with [ H : _ |- _ ] => revert H end.
Tactic Notation "revert" "all" := revert_all.
Ltac revert_except i := repeat match goal with [ H : _ |- _ ] => tryif unify H i then fail else revert H end.
Tactic Notation "revert" "all" "except" ident(i) := revert_except i.
Ltac clear_except i := repeat match goal with [ H : _ |- _ ] => tryif unify H i then fail else clear H end.
Tactic Notation "clear" "all" "except" ident(i) := clear_except i.
Ltac clear_all := repeat match goal with [H : _ |- _] => clear H end.
Ltac remember_arguments E := let tac x := (try (is_var x; fail 1); (*try (is_ftype x; fail 1);*) remember (x)) in repeat (match type of E with | ?t ?x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ _ _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ _ => tac x | ?t ?x _ _ _ _ _ => tac x | ?t ?x _ _ _ _ => tac x | ?t ?x _ _ _ => tac x | ?t ?x _ _ => tac x | ?t ?x _ => tac x | ?t ?x => tac x end).
Ltac clear_dup := match goal with | [ H : ?X |- _ ] => match goal with | [ H' : ?Y |- _ ] => match H with | H' => fail 2 | _ => unify X Y ; (clear H' || clear H) end end end.
Ltac inv_eqs := repeat (match goal with | [ H : @eq _ ?x ?x |- _ ] => fail (* nothing to do on x = x *) | [ H : @eq _ ?x ?y |- _ ] => progress (inversion H; subst; try clear_dup) end).
Ltac clear_trivial_eqs := repeat (progress (match goal with | [ H : @eq _ ?x ?x |- _ ] => clear H end)).
Tactic Notation "general" "induction" hyp(H) := remember_arguments H; revert_except H; induction H; intros; (try inv_eqs); (try clear_trivial_eqs).
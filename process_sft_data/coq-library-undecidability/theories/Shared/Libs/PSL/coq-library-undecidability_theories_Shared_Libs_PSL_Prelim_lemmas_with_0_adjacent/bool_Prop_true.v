Require Export Bool Omega Lia List Setoid Morphisms.
From Undecidability.Shared.Libs.PSL Require Export Tactics.
Global Set Implicit Arguments.
Global Unset Strict Implicit.
Global Unset Printing Records.
Global Unset Printing Implicit Defensive.
Global Set Regular Subst Tactic.
Hint Extern 4 => exact _ : core.
Coercion is_true : bool >-> Sortclass.
Hint Resolve bool_Prop_true bool_Prop_false : core.
Hint Resolve bool_Prop_true' bool_Prop_false' : core.
Definition bool2nat := fun b : bool => if b then 1 else 0.
Definition nat2bool := fun n : nat => match n with 0 => false | _ => true end.
Hint Resolve bool_nat nat_bool : core.
Ltac simpl_coerce := match goal with | [ H: False |- _ ] => destruct H | [ H: ~ is_true true |- _ ] => destruct H; congruence | [ H: is_true false |- _ ] => congruence end.
Ltac simpl_congruence := match goal with | [ H : 0 = S _ |- _] => congruence | [ H : S _ = 0 |- _] => congruence | [ H : S _ = 0 |- _] => congruence | [ H : true = false |- _] => congruence | [ H : false = true |- _] => congruence end.
Hint Extern 1 => simpl_coerce : core.
Hint Extern 1 => simpl_congruence : core.

Lemma bool_Prop_true b : b = true -> b.
Proof.
intros A.
rewrite A.
reflexivity.

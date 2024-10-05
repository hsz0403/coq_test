From Undecidability.L Require Export L Datatypes.LNat Datatypes.LBool Functions.Encoding Computability.Seval.
Require Import Coq.Logic.ConstructiveEpsilon.
Definition cChoice := constructive_indefinite_ground_description_nat_Acc.
Definition bool_enc_inv b:= match b with | lam (lam (var 1)) => true | _ => false end.
Arguments lcomp_comp _{_} _ {_} _ _.

Lemma eq_term_dec (s t : term) : (s = t) + (s <> t).
Proof.
revert t.
induction s; intros t; destruct t; try(right; intros H; inv H; fail).
-
decide (n = n0).
left.
congruence.
right.
congruence.
-
destruct (IHs1 t1), (IHs2 t2); try (right; congruence).
left.
congruence.
-
destruct (IHs t).
left; congruence.
right; congruence.

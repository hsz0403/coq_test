From Undecidability.L Require Import LTactics.
Require Import Undecidability.Shared.Libs.PSL.Vectors.Vectors.
Require Import Vector List.
Import ListNotations.
Import VectorNotations.
Import L_Notations.
Fixpoint many_lam k s := match k with 0 => s | S k => lam (many_lam k s) end.
Fixpoint many_app k s (v : Vector.t term k) := match v with | Vector.nil => s | Vector.cons x _ v => many_app (L.app s x) v end.
Definition many_vars k := (tabulate (n := k) (fun i => k - S (proj1_sig (Fin.to_nat i)))).
Fixpoint many_subst {k} s n (v : Vector.t term k) := match v with | [] => s | Vector.cons u k v => many_subst (subst s (n + k) u) n v end.
From Equations Require Import Equations.

Lemma many_var_in a k : Vector.In a (many_vars k) -> a < k.
Proof.
induction k.
-
inversion 1.
-
intros Ha.
rewrite many_vars_S in Ha.
inv Ha.
+
lia.
+
transitivity k.
2:lia.
eapply IHk.
eapply Eqdep_dec.inj_pair2_eq_dec in H2.
subst.
eauto.
eapply nat_eq_dec.

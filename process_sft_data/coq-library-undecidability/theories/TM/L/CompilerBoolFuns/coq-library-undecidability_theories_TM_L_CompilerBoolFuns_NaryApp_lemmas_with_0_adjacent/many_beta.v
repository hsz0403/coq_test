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

Lemma many_beta k (v : Vector.t term k) s : (forall x, Vector.In x v -> proc x) -> many_app (many_lam k s) v == many_subst s 0 v.
Proof.
induction v in s |- *; cbn; intros Hv.
-
reflexivity.
-
rewrite equiv_many_app_L.
2:{
eapply beta_red.
eapply Hv.
econstructor.
reflexivity.
}
rewrite subst_many_lam.
replace (n + 0) with n by lia.
rewrite IHv.
reflexivity.
intros.
eapply Hv.
now econstructor.

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

Lemma many_subst_many_app (s : term) {k} n (ts v : Vector.t term k) : many_subst (many_app s ts) n v = many_app (many_subst s n v) (Vector.map (fun t => many_subst t n v) ts).
Proof.
induction v in n, s, ts |- *.
-
cbn.
dependent elimination ts.
reflexivity.
-
cbn.
dependent elimination ts.
cbn.
rewrite subst_many_app, IHv.
cbn.
rewrite many_subst_app.
now rewrite Vector.map_map.

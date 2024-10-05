Require Import Reals Psatz.
Require Import mathcomp.ssreflect.ssreflect Rbar.
Require Import Rcomplements.
Require Import Lim_seq Continuity Derive Series.
Require Import Lub Hierarchy.
Open Scope R_scope.
Definition CVS_dom (fn : nat -> R -> R) (D : R -> Prop) := forall x : R, D x -> ex_finite_lim_seq (fun n => fn n x).
Definition CVU_dom (fn : nat -> R -> R) (D : R -> Prop) := forall eps : posreal, eventually (fun n => forall x : R, D x -> Rabs ((fn n x) - real (Lim_seq (fun n => fn n x))) < eps).
Definition CVU_cauchy (fn : nat -> R -> R) (D : R -> Prop) := forall eps : posreal, exists N : nat, forall (n m : nat) (x : R), D x -> (N <= n)%nat -> (N <= m)%nat -> Rabs (fn n x - fn m x) < eps.
Definition is_connected (D : R -> Prop) := forall a b x, D a -> D b -> a <= x <= b -> D x.

Lemma CVU_cont_open (fn : nat -> R -> R) (D : R -> Prop) : open D -> CVU_dom fn D -> (forall n, forall x, D x -> continuity_pt (fn n) x) -> forall x, D x -> continuity_pt (fun y => real (Lim_seq (fun n => fn n y))) x.
Proof.
move => Ho Hfn Hc x Hx.
case: (fun H => CVU_limits_open fn D Ho Hfn H x Hx) => [{x Hx} x n Hx | Hex_s [Hex_f Heq]].
exists (fn n x).
apply is_lim_spec.
intros eps.
case: (Hc n x Hx eps (cond_pos eps)) => {Hc} d [Hd Hc].
exists (mkposreal d Hd) => /= y Hy Hxy.
apply (Hc y).
split.
split.
exact: I.
by apply sym_not_eq, Hxy.
exact: Hy.
apply Lim_correct' in Hex_f.
rewrite -Heq in Hex_f => {Heq}.
replace (Lim_seq (fun n : nat => real (Lim (fn n) x))) with (Lim_seq (fun n : nat => (fn n) x)) in Hex_f.
move => e He.
apply is_lim_spec in Hex_f.
case: (Hex_f (mkposreal e He)) => {Hex_f} /= delta Hex_f.
exists delta ; split => [ | y [[_ Hxy] Hy]].
by apply delta.
apply Hex_f.
exact: Hy.
by apply sym_not_eq.
apply Lim_seq_ext => n.
replace (fn n x) with (real (fn n x)) by auto.
apply sym_eq, f_equal, is_lim_unique.
apply is_lim_spec.
move => eps.
case: (Hc n x Hx eps (cond_pos eps)) => {Hc} d [Hd Hc].
exists (mkposreal d Hd) => /= y Hy Hxy.
apply (Hc y).
split.
split.
exact: I.
by apply sym_not_eq, Hxy.
exact: Hy.

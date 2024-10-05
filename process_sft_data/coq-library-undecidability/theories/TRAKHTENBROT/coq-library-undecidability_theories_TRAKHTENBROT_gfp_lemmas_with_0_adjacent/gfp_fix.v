Require Import List Arith Nat Lia Relations.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list finite php.
From Undecidability.TRAKHTENBROT Require Import notations.
Set Implicit Arguments.
Section gfp.
Variable (M : Type).
Implicit Type (R T : M -> M -> Prop).
Notation "R ⊆ T" := (forall x y, R x y -> T x y).
Notation "R 'o' T" := (fun x z => exists y, R x y /\ T y z) (at level 58).
Let incl_trans R S T : R ⊆ S -> S ⊆ T -> R ⊆ T.
Proof.
firstorder.
Let comp_mono R R' T T' : R ⊆ R' -> T ⊆ T' -> R o T ⊆ R' o T'.
Proof.
firstorder.
Variable (F : (M -> M -> Prop) -> M -> M -> Prop).
Hypothesis (HF0 : forall R T, R ⊆ T -> F R ⊆ F T).
Let sym R := fun x y => R y x.
Let i := iter F (fun _ _ => True).
Let iS n : i (S n) = F (i n).
Proof.
apply iter_S.
Let i0 : i 0 = fun _ _ => True.
Proof.
auto.
Let i_S n : i (S n) ⊆ i n.
Proof.
unfold i.
induction n as [ | n IHn ].
+
simpl; auto.
+
intros ? ?.
rewrite iter_S with (n := n), iter_S.
apply HF0, IHn.
Let i_decr n m : n <= m -> i m ⊆ i n.
Proof.
induction 1; auto.
Definition gfp x y := forall n, i n x y.
Notation I := (@eq M).
Hypothesis HF1 : I ⊆ F I.
Let i_refl n : I ⊆ i n.
Proof.
induction n as [ | n IHn ].
+
rewrite i0; auto.
+
rewrite iS.
apply incl_trans with (1 := HF1), HF0, IHn.
Let gfp_refl : I ⊆ gfp.
Proof.
intros ? ? [] ?; apply i_refl; auto.
Hypothesis HF2 : forall R, sym (F R) ⊆ F (sym R).
Let i_sym n : sym (i n) ⊆ i n.
Proof.
induction n as [ | n IHn ].
+
intros ? ?; rewrite i0; simpl; auto.
+
rewrite iS; apply incl_trans with (2 := HF0 _ IHn), HF2.
Let gfp_sym : sym gfp ⊆ gfp.
Proof.
intros ? ? H ?; apply i_sym, H.
Hypothesis HF3 : forall R, F R o F R ⊆ F (R o R).
Let i_trans n : i n o i n ⊆ i n.
Proof.
induction n as [ | n IHn ].
+
rewrite i0; auto.
+
rewrite iS; apply incl_trans with (1 := @HF3 _), HF0, IHn.
Let gfp_trans : gfp o gfp ⊆ gfp.
Proof.
intros ? ? H ?; apply i_trans.
revert H; apply comp_mono; auto.
Fact gfp_equiv : equiv _ gfp.
Proof.
msplit 2.
+
intro; apply gfp_refl; auto.
+
intros ? y ? ? ?; apply gfp_trans; exists y; auto.
+
intros ? ?; apply gfp_sym.
Fact gfp_greatest R : R ⊆ F R -> R ⊆ gfp.
Proof.
intros HR x y H n; revert x y H.
induction n as [ | n IHn ].
+
now auto.
+
apply incl_trans with (1 := HR).
rewrite iS; apply HF0; auto.
Let gfp_fix1 : F gfp ⊆ gfp.
Proof.
intros ? ? H ?.
apply i_S; rewrite iS.
revert H; apply HF0; auto.
Definition gfp_continuous := forall (s : nat -> M -> M -> Prop), (forall n m, n <= m -> s m ⊆ s n) -> (fun x y => forall n, F (s n) x y) ⊆ F (fun x y => forall n, s n x y).
Variable HF4 : gfp_continuous.
Let gfp_fix0 : gfp ⊆ F gfp.
Proof.
intros ? ? H.
apply HF4; auto.
intro; rewrite <- iS; apply H.
Fact gfp_fix x y : F gfp x y <-> gfp x y.
Proof.
split; auto.
Let dec R := forall x y, { R x y } + { ~ R x y }.
Variable HF5 : forall R, dec R -> dec (F R).
Let i_dec n : dec (i n).
Proof.
induction n as [ | n IHn ].
+
rewrite i0; left; auto.
+
rewrite iS; apply HF5; auto.
Let i_dup n m : n < m -> i n ⊆ i m -> forall k, n <= k -> forall x y, gfp x y <-> i k x y.
Proof.
intros H1 H2.
generalize (i_decr H1) (i_S n); rewrite iS; intros H3 H4.
generalize (incl_trans _ _ _ H2 H3); intros H5.
assert (forall p, i n ⊆ i (p+n)) as H6.
{
induction p as [ | p IHp ]; auto.
simpl plus; rewrite iS.
apply incl_trans with (1 := H5), HF0; auto.
}
intros k Hk x y; split; auto.
intros H a.
destruct (le_lt_dec a k).
+
revert H; apply i_decr; auto.
+
replace a with (a-n+n) by lia.
apply H6.
revert H; apply i_decr; auto.
Let gfp_reached b : (exists n m, n < m <= b /\ i n ⊆ i m) -> (forall x y, gfp x y <-> i b x y).
Proof.
intros (n & m & H1 & H2).
apply i_dup with (2 := H2); auto; try lia.
Variable HF6 : finite_t M.
End gfp.

Fact gfp_fix x y : F gfp x y <-> gfp x y.
Proof.
split; auto.

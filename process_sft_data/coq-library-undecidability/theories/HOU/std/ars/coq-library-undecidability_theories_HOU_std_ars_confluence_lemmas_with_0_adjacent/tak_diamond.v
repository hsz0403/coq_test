Set Implicit Arguments.
Require Import Morphisms FinFun.
From Undecidability.HOU Require Import std.tactics std.misc std.ars.basic.
Set Default Proof Using "Type".
Section Confluence.
Variable X: Type.
Implicit Types (x y z : X) (R S : X -> X -> Prop).
Notation "R <<= S" := (subrelation R S) (at level 70).
Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).
Definition joinable R x y := exists2 z, R x z & R y z.
Definition diamond R := forall x y z, R x y -> R x z -> joinable R y z.
Definition confluent R := diamond (star R).
Definition semi_confluent R := forall x y z, R x y -> star R x z -> joinable (star R) y z.
Fact diamond_semi_confluent R : diamond R -> semi_confluent R.
Proof.
intros H x y1 y2 H1 H2.
revert y1 H1.
induction H2 as [x|x x' y2 H2 _ IH]; intros y1 H1.
-
exists y1; eauto.
-
assert (joinable R y1 x') as [z H3 H4].
{
eapply H; eauto.
}
assert (joinable (star R) z y2) as [u H5 H6].
{
apply IH; auto.
}
exists u; eauto.
Fact confluent_semi R : confluent R <-> semi_confluent R.
Proof.
split.
-
intros H x y1 y2 H1 H2.
eapply H; [|exact H2].
auto.
-
intros H x y1 y2 H1 H2.
revert y2 H2.
induction H1 as [x|x x' y1 H1 _ IH]; intros y2 H2.
+
exists y2; auto.
+
assert (joinable (star R) x' y2) as [z H3 H4].
{
eapply H; eauto.
}
assert (joinable (star R) y1 z) as [u H5 H6].
{
apply IH; auto.
}
exists u; eauto.
Fact diamond_confluent R : diamond R -> confluent R.
Proof.
intros H.
apply confluent_semi, diamond_semi_confluent, H.
Fact joinable_ext R S x y: R === S -> joinable R x y -> joinable S x y.
Proof.
firstorder.
Fact diamond_ext R S: R === S -> diamond S -> diamond R.
Proof.
intros H1 H2 x y z H3 H4.
assert (joinable S y z); firstorder.
End Confluence.
Section Takahashi.
Variables (X: Type) (R: X -> X -> Prop).
Implicit Types (x y z : X).
Notation "x > y" := (R x y) (at level 70).
Notation "x >* y" := (star R x y) (at level 60).
Definition tak_fun rho := forall x y, x > y -> y > rho x.
Variables (rho: X -> X) (tak: tak_fun rho).
Fact tak_diamond : diamond R.
Proof using tak rho.
intros x y z H1 % tak H2 % tak.
exists (rho x); auto.
Fact tak_sound x : Reflexive R -> x > rho x.
Proof using tak.
intros H.
apply tak, H.
Fact tak_mono x y : x > y -> rho x > rho y.
Proof using tak.
intros H % tak % tak.
exact H.
Fact tak_mono_n x y n : x > y -> it n rho x > it n rho y.
Proof using tak.
intros H.
induction n as [|n IH]; cbn.
-
exact H.
-
apply tak_mono, IH.
Fact tak_cofinal x y : x >* y -> exists n, y >* it n rho x.
Proof using tak.
induction 1 as [x |x x' y H _ (n&IH)].
-
exists 0.
cbn.
constructor.
-
exists (S n).
rewrite IH.
cbn.
apply star_exp.
apply tak, tak_mono_n, H.
End Takahashi.
Section TMT.
Notation "R <<= S" := (subrelation R S) (at level 70).
Notation "R === S" := (R <<= S /\ S <<= R) (at level 70).
Variables (X: Type) (R S: X -> X -> Prop) (H1: R <<= S) (H2: S <<= star R).
Fact sandwich_equiv : star R === star S.
Proof using H1 H2.
split.
-
apply star_mono, H1.
-
intros x y H3.
apply star_idem.
revert x y H3.
apply star_mono, H2.
Fact sandwich_confluent : diamond S -> confluent R.
Proof using H1 H2.
intros H3 % diamond_confluent.
revert H3.
apply diamond_ext, sandwich_equiv; auto.
End TMT.

Fact tak_diamond : diamond R.
Proof using tak rho.
intros x y z H1 % tak H2 % tak.
exists (rho x); auto.

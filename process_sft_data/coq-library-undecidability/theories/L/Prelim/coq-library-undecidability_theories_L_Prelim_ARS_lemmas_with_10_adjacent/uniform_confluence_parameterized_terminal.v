Require Export Undecidability.Shared.Libs.PSL.Base Lia.
Module ARSNotations.
Notation "p '<=1' q" := (forall x, p x -> q x) (at level 70).
Notation "p '=1' q" := (forall x, p x <-> q x) (at level 70).
Notation "R '<=2' S" := (forall x y, R x y -> S x y) (at level 70).
Notation "R '=2' S" := (forall x y, R x y <-> S x y) (at level 70).
End ARSNotations.
Import ARSNotations.
Definition rcomp X Y Z (R : X -> Y -> Prop) (S : Y -> Z -> Prop) : X -> Z -> Prop := fun x z => exists y, R x y /\ S y z.
Require Import Arith.
Definition pow X R n : X -> X -> Prop := it (rcomp R) n eq.
Definition functional {X Y} (R: X -> Y -> Prop) := forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.
Definition terminal {X Y} (R: X -> Y -> Prop) x:= forall y, ~ R x y.
Section FixX.
Variable X : Type.
Implicit Types R S : X -> X -> Prop.
Implicit Types x y z : X.
Definition reflexive R := forall x, R x x.
Definition symmetric R := forall x y, R x y -> R y x.
Definition transitive R := forall x y z, R x y -> R y z -> R x z.
Inductive star R : X -> X -> Prop := | starR x : star R x x | starC x y z : R x y -> star R y z -> star R x z.
Definition evaluates R x y := star R x y /\ terminal R y.
Instance star_PO R: PreOrder (star R).
Proof.
constructor;repeat intro;try eapply star_trans; now eauto using star.
Inductive ecl R : X -> X -> Prop := | eclR x : ecl R x x | eclC x y z : R x y -> ecl R y z -> ecl R x z | eclS x y z : R y x -> ecl R y z -> ecl R x z.
Definition joinable R x y := exists z, R x z /\ R y z.
Definition diamond R := forall x y z, R x y -> R x z -> joinable R y z.
Definition confluent R := diamond (star R).
Definition semi_confluent R := forall x y z, R x y -> star R x z -> joinable (star R) y z.
Definition church_rosser R := ecl R <=2 joinable (star R).
Goal forall R, diamond R -> semi_confluent R.
Proof.
intros R A x y z B C.
revert x C y B.
refine (star_simpl_ind _ _).
-
intros y C.
exists y.
eauto using star.
-
intros x x' C D IH y E.
destruct (A _ _ _ C E) as [v [F G]].
destruct (IH _ F) as [u [H I]].
assert (J:= starC G H).
exists u.
eauto using star.
Definition uniform_confluent (R : X -> X -> Prop ) := forall s t1 t2, R s t1 -> R s t2 -> t1 = t2 \/ exists u, R t1 u /\ R t2 u.
Definition classical R x := terminal R x \/ exists y, R x y.
Inductive SN R : X -> Prop := | SNC x : (forall y, R x y -> SN R y) -> SN R x.
Fact SN_unfold R x : SN R x <-> forall y, R x y -> SN R y.
Proof.
split.
-
destruct 1 as [x H].
exact H.
-
intros H.
constructor.
exact H.
End FixX.
Existing Instance star_PO.
Inductive redWithMaxSize {X} (size:X -> nat) (step : X -> X -> Prop): nat -> X -> X -> Prop:= redWithMaxSizeR m s: m = size s -> redWithMaxSize size step m s s | redWithMaxSizeC s s' t m m': step s s' -> redWithMaxSize size step m' s' t -> m = max (size s) m' -> redWithMaxSize size step m s t.
Instance ecl_Equivalence {X} (R:X->X->Prop) : Equivalence (ecl R).
Proof.
split.
-
constructor.
-
apply ecl_sym.
-
apply ecl_trans.
Instance star_ecl_subrel {X} (R:X->X->Prop) : subrelation (star R) (ecl R).
Proof.
intro.
eapply star_ecl.
Instance pow_ecl_subrel {X} (R:X->X->Prop) n : subrelation (pow R n) (ecl R).
Proof.
intros ? ? H%pow_star.
now rewrite H.
Definition computesRel {X Y} (f : X -> option Y) (R:X -> Y -> Prop) := forall x, match f x with Some y => R x y | None => terminal R x end.
Definition evaluatesIn (X : Type) (R : X -> X -> Prop) n (x y : X) := pow R n x y /\ terminal R y.

Lemma uc_terminal R x y z n: uniform_confluent R -> R x y -> pow R n x z -> terminal R z -> exists n' , n = S n' /\ pow R n' y z.
Proof.
intros ? ? ? ter.
edestruct parametrized_semi_confluence as (k&?&?&?&?&R'&?&?).
1-3:now eauto.
destruct k as [|].
-
inv R'.
rewrite <- plus_n_O in *.
eauto.
-
edestruct R' as (?&?&?).
edestruct ter.
Admitted.

Fact SN_unfold R x : SN R x <-> forall y, R x y -> SN R y.
Proof.
split.
-
destruct 1 as [x H].
exact H.
-
intros H.
constructor.
Admitted.

Lemma redWithMaxSize_ge X size step (s t:X) m: redWithMaxSize size step m s t -> size s<= m /\ size t <= m.
Proof.
Admitted.

Lemma redWithMaxSize_trans X size step (s t u:X) m1 m2 m3: redWithMaxSize size step m1 s t -> redWithMaxSize size step m2 t u -> max m1 m2 = m3 -> redWithMaxSize size step m3 s u.
Proof.
induction 1 in m2,u,m3|-*;intros.
-
specialize (redWithMaxSize_ge H0) as [].
revert H1; repeat eapply Nat.max_case_strong; subst m;intros.
all:replace m3 with m2 by lia.
all:eauto.
-
specialize (redWithMaxSize_ge H0) as [].
specialize (redWithMaxSize_ge H2) as [].
eassert (H1':=Max.le_max_l _ _);rewrite H3 in H1'.
eassert (H2':=Max.le_max_r _ _);rewrite H3 in H2'.
econstructor.
eassumption.
eapply IHredWithMaxSize.
eassumption.
reflexivity.
Admitted.

Lemma redWithMaxSize_star {X} f (step : X -> X -> Prop) n x y: redWithMaxSize f step n x y -> star step x y.
Proof.
Admitted.

Lemma terminal_noRed {X} (R:X->X->Prop) x y : terminal R x -> star R x y -> x = y.
Proof.
intros ? R'.
inv R'.
easy.
edestruct H.
Admitted.

Lemma unique_normal_forms {X} (R:X->X->Prop) x y: confluent R -> ecl R x y -> terminal R x -> terminal R y -> x = y.
Proof.
intros CR%confluent_CR E T1 T2.
specialize (CR _ _ E) as (z&R1&R2).
apply terminal_noRed in R1.
apply terminal_noRed in R2.
2-3:eassumption.
Admitted.

Instance ecl_Equivalence {X} (R:X->X->Prop) : Equivalence (ecl R).
Proof.
split.
-
constructor.
-
apply ecl_sym.
-
Admitted.

Instance star_ecl_subrel {X} (R:X->X->Prop) : subrelation (star R) (ecl R).
Proof.
intro.
Admitted.

Instance pow_ecl_subrel {X} (R:X->X->Prop) n : subrelation (pow R n) (ecl R).
Proof.
intros ? ? H%pow_star.
Admitted.

Lemma uniform_confluence_parameterized_both_terminal (X : Type) (R : X -> X -> Prop) (n1 n2 : nat) (s t1 t2 : X): uniform_confluent R -> terminal R t1 -> terminal R t2 -> pow R n1 s t1 -> pow R n2 s t2 -> n1=n2 /\ t1 = t2.
Proof.
intros H1 H2 H2' H3 H4.
specialize (parametrized_confluence H1 H3 H4) as (n0&n'&?&?&?&R'&R''&?).
destruct n0.
destruct n'.
-
inv R'.
inv H5.
split;first [lia | easy].
-
exfalso.
destruct R'' as (?&?&?).
eapply H2'.
eauto.
-
exfalso.
destruct R' as (?&?&?).
eapply H2.
Admitted.

Lemma uniform_confluent_confluent (X : Type) (R : X -> X -> Prop): uniform_confluent R -> confluent R.
Proof.
intros H x y y' Hy Hy'.
apply ARS.star_pow in Hy as (?&Hy).
apply ARS.star_pow in Hy' as (?&Hy').
edestruct parametrized_confluence as (?&?&z&?&?&?&?&?).
eassumption.
exact Hy.
exact Hy'.
exists z.
split;eapply pow_star.
Admitted.

Lemma evalevaluates_evaluatesIn X (step:X->X->Prop) s t: evaluates step s t -> exists k, evaluatesIn step k s t.
Proof.
intros [(R&?)%star_pow ?].
unfold evaluatesIn.
Admitted.

Lemma uniform_confluence_parameterized_terminal (X : Type) (R : X -> X -> Prop) (m n : nat) (s t1 t2 : X): uniform_confluent R -> terminal R t1 -> pow R m s t1 -> pow R n s t2 -> exists n', pow R n' t2 t1 /\ m = n + n'.
Proof.
intros H1 H2 H3 H4.
specialize (parametrized_confluence H1 H3 H4) as (n0&n'&?&?&?&R'&?&?).
destruct n0.
-
inv R'.
exists n'.
intuition.
-
exfalso.
destruct R' as (?&?&?).
eapply H2.
eauto.

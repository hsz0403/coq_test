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

Lemma parametrized_semi_confluence (R : X -> X -> Prop) (m : nat) (s t1 t2 : X) : uniform_confluent R -> pow R m s t1 -> R s t2 -> exists k l u, k <= 1 /\ l <= m /\ pow R k t1 u /\ pow R l t2 u /\ m + k = S l.
Proof.
intros unifConfR; revert s t1 t2; induction m; intros s t1 t2 s_to_t1 s_to_t2.
-
unfold pow in s_to_t1.
simpl in *.
subst s.
exists 1, 0, t2.
repeat split; try lia.
econstructor.
split; try eassumption; econstructor.
-
destruct s_to_t1 as [v [s_to_v v_to_t1]].
destruct (unifConfR _ _ _ s_to_v s_to_t2) as [H | [u [v_to_u t2_to_u]]].
+
subst v.
eexists 0, m, t1; repeat split; try lia; eassumption.
+
destruct (IHm _ _ _ v_to_t1 v_to_u) as [k [l [u' H]]].
eexists k, (S l), u'; repeat split; try lia; try tauto.
econstructor.
split.
eassumption.
tauto.

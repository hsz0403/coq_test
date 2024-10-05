From Undecidability Require Import L.Prelim.MoreBase.
Require Import smpl.Smpl.
Require Export Lia Arith Ring.
From Coq Require Import Setoid.
From Coq Require Import CRelationClasses CMorphisms.
Import CMorphisms.ProperNotations.
From Undecidability.Shared.Libs.PSL Require FinTypes.
Record leUpToC {X} (f g : X -> nat) : Type := { c__leUpToC : nat; correct__leUpToC : forall x, f x <= c__leUpToC * g x }.
Arguments c__leUpToC {_ _ _ H} : rename.
Notation "f <=c g" := (@leUpToC _ f g) (at level 70, g at next level).
Instance leUpToC_preorder X: PreOrder (@leUpToC X).
Proof.
split.
-
exists 1.
intros.
lia.
-
hnf.
intros ? ? ? [c Hc] [c' Hc'].
exists (c*c').
intros.
rewrite Hc,Hc'.
nia.
Instance leUpToC_proper_eq X: Proper (Morphisms.pointwise_relation X eq ==> Morphisms.pointwise_relation X eq ==> arrow) (@leUpToC X).
Proof.
intros ? ? H ? ? H0 H1.
cbv - [iff] in *.
destruct H1.
eexists.
intro.
rewrite <-H, <- H0.
easy.
Instance leUpToC_proper_eq_flip X: Proper (Morphisms.pointwise_relation X eq ==> Morphisms.pointwise_relation X eq ==> flip arrow) (@leUpToC X).
Proof.
intros ? ? H ? ? H0 H1.
cbv - [iff] in *.
destruct H1.
eexists.
intro.
rewrite H, H0.
easy.
Instance le_leUpToC_subrelation X: subrelation (pointwise_relation X le) leUpToC.
Proof.
intros ? ? H.
exists 1.
intros.
hnf in H.
setoid_rewrite H.
nia.
Instance eq_leUpToC_subrelation X: subrelation (pointwise_relation X eq) leUpToC.
Proof.
intros ? ? H.
exists 1.
hnf in H.
setoid_rewrite H.
intros;nia.
Record UpToC {X} (F : X -> nat) : Type := mkUpToC { f__UpToC :> X -> nat; correct__UpToC :> f__UpToC <=c F }.
Add Printing Coercion f__UpToC.
Arguments f__UpToC : clear implicits.
Arguments f__UpToC {_} _ {_}.
Tactic Notation "_applyIfNotConst_nat" tactic(t):= once (match goal with | |- ?R (fun x => ?c) _ => tryif let b := isnatcst c in unify b true then fail 1 else t end).
Smpl Create upToC.
Smpl Add 2 assumption : upToC.
Smpl Add 5 first [simple apply upToC_add | simple apply upToC_mul_c_l | simple apply upToC_mul_c_r | simple apply upToC_max | simple apply upToC_min | progress (simple apply upToC_c) | _applyIfNotConst_nat (simple apply upToC_S)] : upToC.
Smpl Add 4 simple eapply upToC_f__UpToC : upToC.
Ltac smpl_upToC := repeat smpl upToC.
Ltac upToC_le_solve := apply upToC_le;intros ?;nia.
Smpl Create upToC_solve.
Smpl Add upToC_le_solve : upToC_solve.
Ltac smpl_upToC_solve := solve [repeat (smpl upToC);repeat (smpl upToC_solve)].
Tactic Notation "exists_UpToC" uconstr(f) := unshelve (eexists (mkUpToC (f__UpToC:=f) _));cycle 1;[unfold f__UpToC| ].
Tactic Notation "eexists_UpToC" ident(f) := match goal with |- ?Ex (@UpToC ?X ?F) ?P => evar (f : X -> nat);exists_UpToC f end.
Goal (fun x => S x) <=c (fun x => x + 1).
Proof.
timeout 3 (smpl_upToC_solve).
Goal ( { f : UpToC (fun x => x + 1) | forall x, 3 * x + 10 <= f x}).
Proof.
eexists_UpToC f.
-
[f]:intros x.
unfold f.
reflexivity.
-
unfold f.
smpl_upToC_solve.
From Coq Require Strings.String.
Section bla.
Import FinTypes.
End bla.

Instance leUpToC_preorder X: PreOrder (@leUpToC X).
Proof.
split.
-
exists 1.
intros.
lia.
-
hnf.
intros ? ? ? [c Hc] [c' Hc'].
exists (c*c').
intros.
rewrite Hc,Hc'.
Admitted.

Instance leUpToC_proper_eq_flip X: Proper (Morphisms.pointwise_relation X eq ==> Morphisms.pointwise_relation X eq ==> flip arrow) (@leUpToC X).
Proof.
intros ? ? H ? ? H0 H1.
cbv - [iff] in *.
destruct H1.
eexists.
intro.
rewrite H, H0.
Admitted.

Instance le_leUpToC_subrelation X: subrelation (pointwise_relation X le) leUpToC.
Proof.
intros ? ? H.
exists 1.
intros.
hnf in H.
setoid_rewrite H.
Admitted.

Instance eq_leUpToC_subrelation X: subrelation (pointwise_relation X eq) leUpToC.
Proof.
intros ? ? H.
exists 1.
hnf in H.
setoid_rewrite H.
Admitted.

Lemma UpToC_le X F (f : @UpToC X F) : (forall x, f x <= (c__leUpToC (H:=f))*F x).
Proof.
destruct f as [? []];cbn.
Admitted.

Lemma upToC_add X (F f1 f2 :X->nat) : f1 <=c F -> f2 <=c F -> (fun x => f1 x + f2 x) <=c F.
Proof.
intros [c H] [c' H'].
exists (c+c').
intro.
rewrite H,H'.
Admitted.

Lemma upToC_max X (F f1 f2 :X->nat) : f1 <=c F -> f2 <=c F -> (fun x => max (f1 x) (f2 x)) <=c F.
Proof.
intros [c H] [c' H'].
exists (c+c').
intro.
rewrite H,H'.
Admitted.

Lemma upToC_min X (F f1 f2 :X->nat) : f1 <=c F -> f2 <=c F -> (fun x => min (f1 x) (f2 x)) <=c F.
Proof.
intros [c H] [c' H'].
exists (c+c').
intro.
rewrite H,H'.
Admitted.

Lemma upToC_mul_c_l X c (f F : X -> nat): f <=c F -> (fun x => c * f x) <=c F.
Proof.
intros (c'&H).
exists (c'*c).
intros.
rewrite H.
Admitted.

Lemma upToC_mul_c_r X c (f F : X -> nat): f <=c F -> (fun x => f x * c) <=c F.
Proof.
intros (c'&H).
exists (c'*c).
intros.
rewrite H.
Admitted.

Lemma upToC_c X c (F : X -> nat): (fun _ => 1) <=c F -> (fun _ => c ) <=c F.
Proof.
intros H'.
assert (H:c<= 1*c) by lia.
setoid_rewrite H.
eapply upToC_mul_c_r.
Admitted.

Instance leUpToC_proper_eq X: Proper (Morphisms.pointwise_relation X eq ==> Morphisms.pointwise_relation X eq ==> arrow) (@leUpToC X).
Proof.
intros ? ? H ? ? H0 H1.
cbv - [iff] in *.
destruct H1.
eexists.
intro.
rewrite <-H, <- H0.
easy.

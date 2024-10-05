Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProof.
Require Import folProp.
Require Import Deduction.
Section Logic_Rules.
Variable L : Language.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Let equal := equal L.
Let atomic := atomic L.
Let impH := impH L.
Let notH := notH L.
Let forallH := forallH L.
Let orH := orH L.
Let andH := andH L.
Let existH := existH L.
Let iffH := iffH L.
Let ifThenElseH := ifThenElseH L.
Let Prf := Prf L.
Let SysPrf := SysPrf L.
Section Not_Rules.
End Not_Rules.
Section Other_Rules.
End Other_Rules.
End Logic_Rules.

Lemma Axm : forall (T : System) (f : Formula), mem _ T f -> SysPrf T f.
Proof.
intros.
exists (f :: nil).
exists (AXM L f).
intros.
induction H0 as [H0| H0].
rewrite H0 in H.
assumption.
Admitted.

Lemma sysExtend : forall (T U : System) (f : Formula), Included _ T U -> SysPrf T f -> SysPrf U f.
Proof.
intros.
induction H0 as (x, (x0, H0)).
exists x.
exists x0.
intros.
apply H.
apply H0.
Admitted.

Lemma sysWeaken : forall (T : System) (f g : Formula), SysPrf T f -> SysPrf (Ensembles.Add _ T g) f.
Proof.
intros.
apply sysExtend with T.
unfold Included in |- *.
intros.
left.
auto.
Admitted.

Lemma impI : forall (T : System) (f g : Formula), SysPrf (Ensembles.Add _ T g) f -> SysPrf T (impH g f).
Proof.
intros.
apply (DeductionTheorem L).
Admitted.

Lemma impE : forall (T : System) (f g : Formula), SysPrf T (impH g f) -> SysPrf T g -> SysPrf T f.
Proof.
intros.
induction H as (x, (x0, H)).
induction H0 as (x1, (x2, H0)).
set (A1 := MP L _ _ _ _ x0 x2) in *.
exists (x ++ x1).
exists A1.
intros.
Admitted.

Lemma contradiction : forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T (notH f) -> SysPrf T g.
Proof.
intros.
eapply impE with f.
eapply impE with (impH (notH g) (notH f)).
exists (nil (A:=Formula)).
exists (CP L g f).
contradiction.
apply impI.
apply sysWeaken.
assumption.
Admitted.

Lemma nnE : forall (T : System) (f : Formula), SysPrf T (notH (notH f)) -> SysPrf T f.
Proof.
intros.
apply impE with (notH (notH f)).
apply impE with (impH (notH f) (notH (notH (notH f)))).
exists (nil (A:=Formula)).
exists (CP L f (notH (notH f))).
contradiction.
apply impI.
apply contradiction with (notH f).
apply Axm.
right; constructor.
apply sysWeaken.
assumption.
Admitted.

Lemma nnI : forall (T : System) (f : Formula), SysPrf T f -> SysPrf T (notH (notH f)).
Proof.
intros.
apply impE with f.
apply impE with (impH (notH (notH (notH f))) (notH f)).
exists (nil (A:=Formula)).
exists (CP L (notH (notH f)) f).
contradiction.
apply impI.
apply contradiction with f.
apply sysWeaken.
assumption.
apply nnE.
apply Axm; right; constructor.
Admitted.

Lemma cp1 : forall (T : System) (f g : Formula), SysPrf T (impH (notH f) (notH g)) -> SysPrf T (impH g f).
Proof.
intros.
apply impE with (impH (notH f) (notH g)).
exists (nil (A:=Formula)).
exists (CP L f g).
contradiction.
Admitted.

Lemma cp2 : forall (T : System) (f g : Formula), SysPrf T (impH g f) -> SysPrf T (impH (notH f) (notH g)).
Proof.
intros.
apply impE with (impH (notH (notH g)) (notH (notH f))).
exists (nil (A:=Formula)).
exists (CP L (notH g) (notH f)).
contradiction.
apply impI.
apply nnI.
apply impE with g.
apply sysWeaken.
assumption.
apply nnE.
Admitted.

Lemma orI1 : forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T (orH f g).
Proof.
intros.
unfold orH, fol.orH in |- *.
apply impI.
apply contradiction with f.
apply sysWeaken.
assumption.
Admitted.

Lemma orI2 : forall (T : System) (f g : Formula), SysPrf T g -> SysPrf T (orH f g).
Proof.
intros.
unfold orH, fol.orH in |- *.
apply impI.
apply sysWeaken.
Admitted.

Lemma orE : forall (T : System) (f g h : Formula), SysPrf T (orH f g) -> SysPrf T (impH f h) -> SysPrf T (impH g h) -> SysPrf T h.
Proof.
intros.
unfold orH, fol.orH in H.
apply impE with (impH h h).
apply cp1.
apply impE with (impH (notH h) h).
apply impI.
apply impI.
apply contradiction with h.
apply impE with (notH h).
apply Axm; left; right; constructor.
apply Axm; right; constructor.
apply Axm; right; constructor.
apply impI.
apply impE with g.
apply sysWeaken; assumption.
apply impE with (notH f).
apply sysWeaken; assumption.
apply impE with (notH h).
apply cp2.
apply sysWeaken; assumption.
apply Axm; right; constructor.
apply impI.
Admitted.

Lemma orSys : forall (T : System) (f g h : Formula), SysPrf (Ensembles.Add _ T f) h -> SysPrf (Ensembles.Add _ T g) h -> SysPrf (Ensembles.Add _ T (orH f g)) h.
Proof.
intros.
eapply orE.
apply Axm; right; constructor.
apply sysWeaken.
apply impI.
assumption.
apply sysWeaken.
apply impI.
Admitted.

Lemma andI : forall (T : System) (f g : Formula), SysPrf T f -> SysPrf T g -> SysPrf T (andH f g).
Proof.
intros.
unfold andH, fol.andH in |- *.
apply orE with (notH (orH (notH f) (notH g))) (orH (notH f) (notH g)).
apply noMiddle.
apply impI.
apply Axm; right; constructor.
apply impI.
apply orE with (notH f) (notH g).
apply Axm; right; constructor.
apply cp2.
apply impI.
repeat apply sysWeaken.
assumption.
apply cp2.
apply impI.
repeat apply sysWeaken.
Admitted.

Lemma andE1 : forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T f.
Proof.
intros.
apply nnE.
apply impE with (andH f g).
unfold andH, fol.andH in |- *.
apply cp2.
apply impI.
apply orI1.
apply Axm; right; constructor.
Admitted.

Lemma andE2 : forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T g.
Proof.
intros.
apply nnE.
apply impE with (andH f g).
unfold andH, fol.andH in |- *.
apply cp2.
apply impI.
apply orI2.
apply Axm; right; constructor.
Admitted.

Lemma noMiddle : forall (T : System) (f : Formula), SysPrf T (orH (notH f) f).
Proof.
intros.
unfold orH, fol.orH in |- *.
apply impI.
apply nnE.
apply Axm; right; constructor.

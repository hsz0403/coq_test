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

Lemma noMiddle : forall (T : System) (f : Formula), SysPrf T (orH (notH f) f).
Proof.
intros.
unfold orH, fol.orH in |- *.
apply impI.
apply nnE.
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

Lemma iffI : forall (T : System) (f g : Formula), SysPrf T (impH f g) -> SysPrf T (impH g f) -> SysPrf T (iffH f g).
Proof.
intros.
unfold iffH, fol.iffH in |- *.
Admitted.

Lemma iffE1 : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (impH f g).
Proof.
intros.
unfold iffH, fol.iffH in H.
eapply andE1.
Admitted.

Lemma iffE2 : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (impH g f).
Proof.
intros.
unfold iffH, fol.iffH in H.
eapply andE2.
Admitted.

Lemma forallI : forall (T : System) (f : Formula) (v : nat), ~ In_freeVarSys L v T -> SysPrf T f -> SysPrf T (forallH v f).
Proof.
intros.
induction H0 as (x, H0); induction H0 as (x0, H0).
exists x.
assert (~ In v (freeVarListFormula L x)).
unfold not in |- *; intros; elim H.
induction (In_freeVarListFormulaE _ _ _ H1).
exists x1.
split.
tauto.
apply H0.
tauto.
exists (GEN L _ _ _ H1 x0).
Admitted.

Lemma forallE : forall (T : System) (f : Formula) (v : nat) (t : Term), SysPrf T (forallH v f) -> SysPrf T (substituteFormula L f v t).
Proof.
intros.
apply impE with (forallH v f).
exists (nil (A:=Formula)).
exists (FA1 L f v t).
contradiction.
Admitted.

Lemma forallSimp : forall (T : System) (f : Formula) (v : nat), SysPrf T (forallH v f) -> SysPrf T f.
Proof.
intros.
rewrite <- subFormulaId with L f v.
apply forallE.
Admitted.

Lemma existI : forall (T : System) (f : Formula) (v : nat) (t : Term), SysPrf T (substituteFormula L f v t) -> SysPrf T (existH v f).
Proof.
intros.
unfold existH, fol.existH in |- *.
apply impE with (notH (notH (substituteFormula L f v t))).
apply cp2.
apply impI.
rewrite <- (subFormulaNot L).
apply forallE.
apply Axm; right; constructor.
apply nnI.
Admitted.

Lemma existE : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys L v T -> ~ In v (freeVarFormula L g) -> SysPrf T (existH v f) -> SysPrf T (impH f g) -> SysPrf T g.
Proof.
intros.
unfold existH, fol.existH in H1.
apply nnE.
apply impE with (fol.notH L (fol.forallH L v (fol.notH L f))).
apply cp2.
apply impI.
apply impE with (forallH v (notH g)).
apply impE with (forallH v (impH (notH g) (notH f))).
exists (nil (A:=Formula)).
exists (FA3 L (notH g) (notH f) v).
contradiction.
apply sysWeaken.
apply forallI.
auto.
apply cp2.
assumption.
apply impE with (notH g).
exists (nil (A:=Formula)).
exists (FA2 L (notH g) v H0).
contradiction.
apply Axm; right; constructor.
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
assumption.

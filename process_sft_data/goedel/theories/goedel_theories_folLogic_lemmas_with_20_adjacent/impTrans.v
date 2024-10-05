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

Lemma existSimp : forall (T : System) (f : Formula) (v : nat), SysPrf T f -> SysPrf T (existH v f).
Proof.
intros.
eapply existI.
rewrite subFormulaId.
Admitted.

Lemma existSys : forall (T : System) (f g : Formula) (v : nat), ~ In_freeVarSys L v T -> ~ In v (freeVarFormula L g) -> SysPrf (Ensembles.Add _ T f) g -> SysPrf (Ensembles.Add _ T (existH v f)) g.
Proof.
intros.
eapply existE.
unfold not in |- *; intros; elim H.
induction H2 as (x, H2).
exists x.
induction H2 as (H2, H3).
split.
apply H2.
induction H3 as [x H3| x H3].
assumption.
induction H3.
simpl in H2.
absurd (v = v).
eapply In_list_remove2.
apply H2.
auto.
assumption.
apply Axm; right; constructor.
apply sysWeaken.
apply impI.
Admitted.

Lemma absurd1 : forall (T : System) (f : Formula), SysPrf T (impH f (notH f)) -> SysPrf T (notH f).
Proof.
intros.
apply orE with (notH f) f.
apply noMiddle.
apply impI.
apply Axm; right; constructor.
Admitted.

Lemma nImp : forall (T : System) (f g : Formula), SysPrf T (andH f (notH g)) -> SysPrf T (notH (impH f g)).
Proof.
intros.
apply absurd1.
apply impI.
apply contradiction with g.
apply impE with f.
apply Axm; right; constructor.
eapply andE1.
apply sysWeaken.
apply H.
apply sysWeaken.
eapply andE2.
Admitted.

Lemma nOr : forall (T : System) (f g : Formula), SysPrf T (andH (notH f) (notH g)) -> SysPrf T (notH (orH f g)).
Proof.
intros.
apply absurd1.
apply impI.
apply orSys.
apply contradiction with f.
apply Axm; right; constructor.
apply sysWeaken.
eapply andE1.
apply H.
apply contradiction with g.
apply Axm; right; constructor.
apply sysWeaken.
eapply andE2.
Admitted.

Lemma nAnd : forall (T : System) (f g : Formula), SysPrf T (orH (notH f) (notH g)) -> SysPrf T (notH (andH f g)).
Proof.
intros.
unfold andH, fol.andH in |- *.
apply nnI.
Admitted.

Lemma nForall : forall (T : System) (f : Formula) (v : nat), SysPrf T (existH v (notH f)) -> SysPrf T (notH (forallH v f)).
Proof.
intros.
apply impE with (existH v (notH f)).
apply sysExtend with (Empty_set Formula).
unfold Included in |- *.
intros.
induction H0.
apply impI.
apply existSys.
unfold not in |- *; intros.
induction H0 as (x, H0); induction H0 as (H0, H1).
induction H1.
simpl in |- *.
unfold not in |- *; intro.
absurd (v = v).
eapply In_list_remove2.
apply H0.
reflexivity.
apply impE with (notH f).
apply cp2.
apply sysWeaken.
apply impI.
eapply forallSimp.
apply Axm; right; constructor.
apply Axm; right; constructor.
Admitted.

Lemma nExist : forall (T : System) (f : Formula) (v : nat), SysPrf T (forallH v (notH f)) -> SysPrf T (notH (existH v f)).
Proof.
intros.
unfold existH, fol.existH in |- *.
apply nnI.
Admitted.

Lemma impRefl : forall (T : System) (f : Formula), SysPrf T (impH f f).
Proof.
intros.
apply impI.
Admitted.

Lemma orSym : forall (T : System) (f g : Formula), SysPrf T (orH f g) -> SysPrf T (orH g f).
Proof.
intros.
eapply orE.
apply H.
apply impI.
apply orI2.
apply Axm; right; constructor.
apply impI.
apply orI1.
Admitted.

Lemma andSym : forall (T : System) (f g : Formula), SysPrf T (andH f g) -> SysPrf T (andH g f).
Proof.
intros.
apply andI.
eapply andE2.
apply H.
eapply andE1.
Admitted.

Lemma iffRefl : forall (T : System) (f : Formula), SysPrf T (iffH f f).
Proof.
intros.
apply iffI.
apply impRefl.
Admitted.

Lemma iffSym : forall (T : System) (f g : Formula), SysPrf T (iffH f g) -> SysPrf T (iffH g f).
Proof.
unfold iffH, fol.iffH in |- *.
intros.
apply andSym.
Admitted.

Lemma iffTrans : forall (T : System) (f g h : Formula), SysPrf T (iffH f g) -> SysPrf T (iffH g h) -> SysPrf T (iffH f h).
Proof.
intros.
apply iffI.
eapply impTrans.
apply iffE1.
apply H.
apply iffE1.
apply H0.
eapply impTrans.
apply iffE2.
apply H0.
apply iffE2.
Admitted.

Lemma openClosed : forall (T : System) (f : Formula), SysPrf T (close L f) -> SysPrf T f.
Proof.
intros T f.
unfold close in |- *.
generalize (no_dup nat Peano_dec.eq_nat_dec (freeVarFormula L f)).
intros.
induction l as [| a l Hrecl].
apply H.
simpl in H.
apply Hrecl.
eapply forallSimp.
Admitted.

Lemma impTrans : forall (T : System) (f g h : Formula), SysPrf T (impH f g) -> SysPrf T (impH g h) -> SysPrf T (impH f h).
Proof.
intros.
apply impI.
apply impE with g.
apply sysWeaken.
apply H0.
apply impE with f.
apply sysWeaken.
apply H.
apply Axm; right; constructor.

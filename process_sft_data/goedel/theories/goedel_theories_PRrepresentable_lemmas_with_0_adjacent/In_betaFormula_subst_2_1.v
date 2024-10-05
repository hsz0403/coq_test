Require Import Arith.
Require Import extEqualNat.
Require Import subAll.
Require Import folProp.
Require Import subProp.
Require Import folReplace.
Require Import folLogic3.
Require Import NN.
Require Import NNtheory.
Require Import primRec.
Require Import chRem.
Require Import expressible.
Require Import Coq.Lists.List.
Require Vector.
Require Import ListExt.
Require Import cPair.
Require Import Decidable.
Section Primative_Recursive_Representable.
Let Representable := Representable NN.
Let RepresentableAlternate := RepresentableAlternate NN closedNN1.
Let RepresentableHelp := RepresentableHelp NN.
Let Representable_ext := Representable_ext NN.
Definition beta (a z : nat) : nat := snd (proj1_sig (modulo (coPrimeBeta z (cPairPi1 a)) (gtBeta z (cPairPi1 a)) (cPairPi2 a))).
Definition betaFormula : Formula := existH 3 (andH (LT (var 3) (Succ (var 2))) (existH 4 (andH (LT (var 4) (Succ (var 2))) (andH (equal (Plus (Times (Plus (var 3) (var 4)) (Succ (Plus (var 3) (var 4)))) (Times (natToTerm 2) (var 3))) (Times (natToTerm 2) (var 2))) (andH (LT (var 0) (Succ (Times (var 3) (Succ (var 1))))) (existH 5 (andH (LT (var 5) (Succ (var 4))) (equal (Plus (var 0) (Times (var 5) (Succ (Times (var 3) (Succ (var 1)))))) (var 4))))))))).
Fixpoint addExists (m n : nat) (f : Formula) {struct n} : Formula := match n with | O => f | S n' => existH (n' + m) (addExists m n' f) end.
Fixpoint addForalls (m n : nat) (f : Formula) {struct n} : Formula := match n with | O => f | S n' => forallH (n' + m) (addForalls m n' f) end.
Fixpoint FormulasToFormula (n w m : nat) (vs : Vector.t (Formula * naryFunc n) m) {struct vs} : Formula := match vs with | Vector.nil => equal (var 0) (var 0) | Vector.cons v m' vs' => andH (substituteFormula LNN (fst v) 0 (var (S m' + w))) (FormulasToFormula n w m' vs') end.
Fixpoint FormulasToFuncs (n m : nat) (vs : Vector.t (Formula * naryFunc n) m) {struct vs} : Vector.t (naryFunc n) m := match vs in (Vector.t _ m) return (Vector.t (naryFunc n) m) with | Vector.nil => Vector.nil _ | Vector.cons v m' vs' => Vector.cons _ (snd v) m' (FormulasToFuncs n m' vs') end.
Fixpoint RepresentablesHelp (n m : nat) (vs : Vector.t (Formula * naryFunc n) m) {struct vs} : Prop := match vs with | Vector.nil => True | Vector.cons a m' vs' => RepresentableHelp _ (snd a) (fst a) /\ RepresentablesHelp n m' vs' end.
Let succFormula : Formula := equal (var 0) (Succ (var 1)).
Remark succRepresentable : Representable 1 S succFormula.
Proof.
intros.
unfold Representable in |- *.
split.
intros.
simpl in H.
decompose sum H.
rewrite <- H0.
auto.
rewrite <- H1.
auto.
simpl in |- *.
intros.
unfold succFormula in |- *.
rewrite (subFormulaEqual LNN).
simpl in |- *.
apply iffRefl.
Let zeroFormula : Formula := equal (var 0) Zero.
Remark zeroRepresentable : Representable 0 0 zeroFormula.
Proof.
intros.
unfold Representable in |- *.
split.
intros.
simpl in H.
decompose sum H.
rewrite <- H0.
auto.
simpl in |- *.
apply iffRefl.
Let projFormula (m : nat) : Formula := equal (var 0) (var (S m)).
Remark projRepresentable : forall (n m : nat) (pr : m < n), Representable n (evalProjFunc n m pr) (projFormula m).
Proof.
intros.
unfold Representable in |- *.
split.
intros.
simpl in H.
decompose sum H.
rewrite <- H0.
apply le_O_n.
rewrite <- H1.
apply lt_n_Sm_le.
apply lt_n_S.
auto.
induction n as [| n Hrecn].
elim (lt_n_O m pr).
simpl in |- *.
intros.
induction (Nat.eq_dec m n).
rewrite a0.
clear a0 Hrecn pr m.
induction n as [| n Hrecn].
simpl in |- *.
unfold projFormula in |- *.
rewrite (subFormulaEqual LNN).
simpl in |- *.
apply iffRefl.
simpl in |- *.
intros.
unfold projFormula in |- *.
repeat rewrite (subFormulaEqual LNN).
simpl in |- *.
induction (match match Nat.eq_dec n n with | left e => left (f_equal_nat nat S n n e) | right n0 => right (not_eq_S n n n0) end with | left _ => _ | right _ => _ end).
simpl in |- *.
replace (fol.equal LNN (fol.var LNN 0) (substituteTerm LNN (natToTerm a) (S n) (natToTerm a0))) with (substituteFormula LNN (equal (var 0) (var (S n))) (S n) (natToTerm a)).
auto.
rewrite (subFormulaEqual LNN).
simpl in |- *.
induction (match Nat.eq_dec n n with | left e => left (f_equal_nat nat S n n e) | right n0 => right (not_eq_S n n n0) end).
rewrite subTermNil.
reflexivity.
apply closedNatToTerm.
elim b.
auto.
elim b.
auto.
generalize match le_lt_or_eq m n (lt_n_Sm_le m n pr) with | or_introl l2 => l2 | or_intror l2 => False_ind (m < n) (b l2) end.
intros.
apply RepresentableAlternate with (equal (var 0) (var (S m))).
apply iffSym.
apply (subFormulaNil LNN).
simpl in |- *.
unfold not in |- *; intros.
decompose sum H.
discriminate H0.
inversion H1.
elim (lt_irrefl n).
rewrite H2 in l.
auto.
auto.
Let composeSigmaFormula (n w m : nat) (A : Vector.t (Formula * naryFunc n) m) (B : Formula) : Formula := addExists (S w) m (andH (FormulasToFormula n w m A) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S x' + w) end))).
Remark composeSigmaRepresentable : forall n w m : nat, n <= w -> forall (A : Vector.t (Formula * naryFunc n) m) (B : Formula) (g : naryFunc m), RepresentablesHelp n m A -> Vector.t_rect (Formula * naryFunc n) (fun _ _ => Prop) True (fun (pair : Formula * naryFunc n) (m : nat) (v : Vector.t _ m) (rec : Prop) => (forall v : nat, In v (freeVarFormula LNN (fst pair)) -> v <= n) /\ rec) m A -> Representable m g B -> Representable n (evalComposeFunc n m (FormulasToFuncs n m A) g) (composeSigmaFormula n w m A B).
Proof.
assert (forall n w m : nat, n <= w -> forall (A : Vector.t (Formula * naryFunc n) m) (B : Formula) (g : naryFunc m), RepresentablesHelp n m A -> Vector.t_rect (Formula * naryFunc n) (fun _ _ => Prop) True (fun (pair : Formula * naryFunc n) (m : nat) (v : Vector.t _ m) (rec : Prop) => (forall v : nat, In v (freeVarFormula LNN (fst pair)) -> v <= n) /\ rec) m A -> Representable m g B -> RepresentableHelp n (evalComposeFunc n m (FormulasToFuncs n m A) g) (composeSigmaFormula n w m A B)).
intro.
induction n as [| n Hrecn]; simpl in |- *.
intros w m H v.
induction v as [| a n v Hrecv]; simpl in |- *; intros.
unfold composeSigmaFormula in |- *.
simpl in |- *.
replace (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)) with (subAllFormula LNN B (fun x : nat => var x)).
apply iffTrans with B.
apply iffTrans with (subAllFormula LNN B (fun x : nat => var x)).
apply iffI; apply impI.
eapply andE2.
apply Axm; right; constructor.
apply andI.
apply eqRefl.
apply Axm; right; constructor.
apply (subAllFormulaId LNN).
induction H2 as (H2, H3).
auto.
apply subAllFormula_ext.
intros.
destruct m as [| n].
auto.
elim (le_Sn_O n).
induction H2 as (H2, H4).
apply H2.
auto.
induction H0 as (H0, H3).
induction H1 as (H1, H4).
induction H2 as (H2, H5).
assert (forall a : nat, SysPrf NN (iffH (composeSigmaFormula 0 w n v (substituteFormula LNN B (S n) (natToTerm a))) (equal (var 0) (natToTerm (evalList n (FormulasToFuncs 0 n v) (g a)))))).
intros.
apply Hrecv.
auto.
auto.
split.
intros.
induction (freeVarSubFormula3 _ _ _ _ _ H6).
assert (In v0 (freeVarFormula LNN B)).
eapply In_list_remove1.
apply H7.
induction (le_lt_or_eq _ _ (H2 _ H8)).
apply lt_n_Sm_le.
auto.
elim (In_list_remove2 _ _ _ _ _ H7).
auto.
elim (closedNatToTerm _ _ H7).
apply H5.
clear Hrecv.
unfold composeSigmaFormula in |- *.
unfold composeSigmaFormula in H6.
simpl in |- *.
apply iffTrans with (addExists (S w) n (andH (FormulasToFormula 0 w n v) (subAllFormula LNN (substituteFormula LNN B (S n) (natToTerm (snd a))) (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)))); [ idtac | apply H6 ].
clear H6.
apply iffTrans with (existH (n + S w) (addExists (S w) n (andH (andH (substituteFormula LNN (equal (var 0) (natToTerm (snd a))) 0 (var (S (n + w)))) (FormulasToFormula 0 w n v)) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end))))).
apply (reduceExist LNN).
apply closedNN.
apply reduceAddExists.
repeat apply (reduceAnd LNN); try apply iffRefl.
apply (reduceSub LNN).
apply closedNN.
auto.
rewrite (subFormulaEqual LNN).
rewrite (subTermVar1 LNN).
rewrite (subTermNil LNN).
apply iffTrans with (existH (n + S w) (andH (fol.equal LNN (var (S (n + w))) (natToTerm (snd a))) (addExists (S w) n (andH (FormulasToFormula 0 w n v) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)))))).
apply (reduceExist LNN).
apply closedNN.
apply iffI.
apply impI.
apply andI.
cut (SysPrf (Ensembles.Add (fol.Formula LNN) NN (andH (andH (fol.equal LNN (var (S (n + w))) (natToTerm (snd a))) (FormulasToFormula 0 w n v)) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)))) (fol.equal LNN (var (S (n + w))) (natToTerm (snd a)))).
generalize (andH (andH (fol.equal LNN (var (S (n + w))) (natToTerm (snd a))) (FormulasToFormula 0 w n v)) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end))).
cut (n + w < S (n + w)).
generalize (S (n + w)).
intros.
clear H5 H2 H4 H1 H3 H0 g B v.
induction n as [| n Hrecn].
simpl in |- *.
auto.
simpl in |- *.
apply existSys.
apply closedNN.
simpl in |- *; unfold not in |- *; intros.
induction H0 as [H0| H0].
rewrite H0 in H6.
rewrite <- plus_Snm_nSm in H6.
elim (lt_irrefl _ H6).
elim (closedNatToTerm _ _ H0).
apply Hrecn.
eapply lt_trans.
apply lt_n_Sn.
auto.
apply lt_n_Sn.
eapply andE1.
eapply andE1.
apply Axm; right; constructor.
apply impE with (addExists (S w) n (andH (andH (fol.equal LNN (var (S (n + w))) (natToTerm (snd a))) (FormulasToFormula 0 w n v)) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)))).
apply sysWeaken.
apply reduceAddExistsOneWay.
apply impI.
apply andI.
eapply andE2.
eapply andE1.
apply Axm; right; constructor.
eapply andE2.
apply Axm; right; constructor.
apply Axm; right; constructor.
apply impI.
apply impE with (addExists (S w) n (andH (FormulasToFormula 0 w n v) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)))).
apply impE with (fol.equal LNN (var (S (n + w))) (natToTerm (snd a))).
apply sysWeaken.
apply impI.
cut (SysPrf (Ensembles.Add (fol.Formula LNN) NN (fol.equal LNN (var (S (n + w))) (natToTerm (snd a)))) (impH (andH (FormulasToFormula 0 w n v) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end))) (andH (andH (fol.equal LNN (var (S (n + w))) (natToTerm (snd a))) (FormulasToFormula 0 w n v)) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end))))).
generalize (andH (FormulasToFormula 0 w n v) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end))) (andH (andH (fol.equal LNN (var (S (n + w))) (natToTerm (snd a))) (FormulasToFormula 0 w n v)) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end))).
cut (n + w < S (n + w)).
generalize (S (n + w)).
clear H5 H2 H4 H1 H3 H0 g B v.
induction n as [| n Hrecn].
auto.
simpl in |- *.
intros.
apply impI.
apply existSys.
unfold not in |- *; intros.
induction H2 as (x, H2); induction H2 as (H2, H3).
induction H3 as [x H3| x H3].
elim (closedNN (n + S w)).
exists x.
auto.
induction H3.
simpl in H2.
induction H2 as [H2| H2].
rewrite <- plus_Snm_nSm in H2.
rewrite H2 in H0.
elim (lt_irrefl _ H0).
elim (closedNatToTerm _ _ H2).
simpl in |- *.
unfold not in |- *; intros.
elim (In_list_remove2 _ _ _ _ _ H2).
auto.
apply existSimp.
apply impE with (addExists (S w) n f).
apply sysWeaken.
apply Hrecn; auto.
eapply lt_trans.
apply lt_n_Sn.
auto.
apply Axm; right; constructor.
apply lt_n_Sn.
apply impI.
repeat apply andI.
apply Axm; left; right; constructor.
eapply andE1.
apply Axm; right; constructor.
eapply andE2.
apply Axm; right; constructor.
eapply andE1.
apply Axm; right; constructor.
eapply andE2.
apply Axm; right; constructor.
apply iffTrans with (substituteFormula LNN (addExists (S w) n (andH (FormulasToFormula 0 w n v) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)))) (S n + w) (natToTerm (snd a))).
apply iffI.
apply impI.
apply existSys.
apply closedNN.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H6).
elim (In_list_remove2 _ _ _ _ _ H7).
symmetry in |- *.
apply plus_Snm_nSm.
elim (closedNatToTerm _ _ H7).
apply impE with (substituteFormula LNN (addExists (S w) n (andH (FormulasToFormula 0 w n v) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)))) (S n + w) (var (S n + w))).
apply (subWithEquals LNN).
eapply andE1.
apply Axm; right; constructor.
rewrite (subFormulaId LNN).
eapply andE2.
apply Axm; right; constructor.
apply impI.
apply existI with (natToTerm (snd a)).
rewrite (subFormulaAnd LNN).
rewrite <- plus_Snm_nSm.
apply andI.
rewrite subFormulaEqual.
rewrite (subTermVar1 LNN).
rewrite (subTermNil LNN).
apply eqRefl.
apply closedNatToTerm.
apply Axm; right; constructor.
rewrite subAddExistsNice.
apply reduceAddExists.
rewrite (subFormulaAnd LNN).
apply (reduceAnd LNN).
apply (subFormulaNil LNN).
cut (n + w < S n + w).
generalize (S n + w).
clear H5 H3 g H2.
induction v as [| a0 n v Hrecv]; unfold not in |- *; intros.
simpl in H3.
decompose sum H3.
rewrite <- H5 in H2.
elim (lt_n_O _ H2).
rewrite <- H6 in H2.
elim (lt_n_O _ H2).
simpl in H3.
induction (in_app_or _ _ _ H3).
simpl in H4.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (le_not_lt n0 0).
decompose record H4.
apply H7.
eapply In_list_remove1.
apply H6.
apply lt_trans with (S n + w).
simpl in |- *; apply lt_O_Sn.
auto.
induction H6 as [H6| H6].
rewrite <- H6 in H2.
elim (lt_irrefl _ H2).
elim H6.
lazymatch goal with _ : In ?n _ |- _ => elim Hrecv with n end.
simpl in H4.
tauto.
eapply lt_trans.
apply lt_n_Sn.
auto.
auto.
simpl in |- *.
apply lt_n_Sn.
eapply iffTrans.
apply (subSubAllFormula LNN).
apply iffSym.
eapply iffTrans.
apply (subAllSubFormula LNN).
replace (subAllFormula LNN B (fun n1 : nat => substituteTerm LNN match n1 with | O => var 0 | S x' => var (S (x' + w)) end (S n + w) (natToTerm (snd a)))) with (subAllFormula LNN B (fun x : nat => match eq_nat_dec (S n) x with | left _ => subAllTerm LNN (natToTerm (snd a)) (fun x0 : nat => match x0 with | O => var 0 | S x' => var (S (x' + w)) end) | right _ => (fun x0 : nat => match x0 with | O => var 0 | S x' => var (S (x' + w)) end) x end)).
apply iffRefl.
apply subAllFormula_ext.
intros.
induction (eq_nat_dec (S n) m).
rewrite <- a0.
rewrite (subTermVar1 LNN).
clear H0.
induction (snd a).
simpl in |- *.
reflexivity.
simpl in |- *.
rewrite IHn0.
reflexivity.
destruct m as [| n0].
simpl in |- *.
reflexivity.
rewrite (subTermVar2 LNN).
reflexivity.
unfold not in |- *; intros; elim b.
apply plus_reg_l with w.
repeat rewrite (plus_comm w).
apply H7.
left.
rewrite <- plus_Snm_nSm.
apply le_n.
intros.
elim (closedNatToTerm _ _ H6).
apply closedNatToTerm.
intros.
set (v' := Vector.t_rec (Formula * (nat -> naryFunc n)) (fun (m : nat) (v : Vector.t _ m) => Vector.t (Formula * naryFunc n) m) (Vector.nil _) (fun (pair : Formula * (nat -> naryFunc n)) (m : nat) (v : Vector.t _ m) (rec : Vector.t (Formula * naryFunc n) m) => Vector.cons _ (substituteFormula LNN (fst pair) (S n) (natToTerm a), snd pair a) m rec) _ A) in *.
assert (RepresentableHelp n (evalComposeFunc n m (FormulasToFuncs n m v') g) (addExists (S w) m (andH (FormulasToFormula n w m v') (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end))))).
unfold composeSigmaFormula in Hrecn.
simpl in Hrecn.
apply Hrecn.
eapply le_trans.
apply le_n_Sn.
auto.
clear B g H2.
induction A as [| a0 n0 A HrecA]; simpl in (value of v'); simpl in |- *.
auto.
split.
simpl in H0.
induction H0 as (H0, H2).
apply H0.
apply HrecA.
induction H0 as (H0, H2).
auto.
simpl in H1.
induction H1 as (H1, H2).
auto.
simpl in H1.
clear H2 H0 g B.
induction A as [| a0 n0 A HrecA].
simpl in |- *.
auto.
simpl in |- *.
split.
simpl in H1.
induction H1 as (H0, H1).
intros.
induction (freeVarSubFormula3 _ _ _ _ _ H2).
assert (v <= S n).
apply H0.
eapply In_list_remove1.
apply H3.
induction (le_lt_or_eq _ _ H4).
apply lt_n_Sm_le.
auto.
elim (In_list_remove2 _ _ _ _ _ H3).
auto.
elim (closedNatToTerm _ _ H3).
apply HrecA.
induction H1 as (H0, H1).
auto.
auto.
unfold composeSigmaFormula in |- *.
clear Hrecn.
apply RepresentableAlternate with (addExists (S w) m (andH (FormulasToFormula n w m v') (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S (x' + w)) end)))).
rewrite subAddExistsNice.
apply reduceAddExists.
rewrite (subFormulaAnd LNN).
apply (reduceAnd LNN).
clear H3 H2 H1 H0 g B.
induction A as [| a0 n0 A HrecA].
simpl in |- *.
apply iffSym.
apply (subFormulaNil LNN).
simpl in |- *.
unfold not in |- *; intros.
decompose sum H0.
discriminate H1.
discriminate H2.
simpl in |- *.
rewrite (subFormulaAnd LNN).
apply (reduceAnd LNN); [ idtac | apply HrecA ].
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
unfold not in |- *; intros.
induction H0 as [H0| H0].
rewrite <- H0 in H.
elim (le_not_lt _ _ H).
apply le_lt_n_Sm.
apply le_plus_r.
apply H0.
apply iffSym.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
decompose record (freeVarSubAllFormula1 _ _ _ _ H4).
destruct x as [| n0].
induction H7 as [H5| H5].
discriminate H5.
elim H5.
induction H7 as [H5| H5].
rewrite <- H5 in H.
elim (le_not_lt _ _ H).
apply le_lt_n_Sm.
apply le_plus_r.
apply H5.
right.
apply le_lt_n_Sm.
auto.
intros.
elim (closedNatToTerm _ _ H4).
apply Representable_ext with (evalComposeFunc n m (FormulasToFuncs n m v') g).
clear H3 H2 H1 H0 B.
apply extEqualCompose.
unfold extEqualVector in |- *.
clear g.
induction A as [| a0 n0 A HrecA]; simpl in |- *.
auto.
split.
apply extEqualRefl.
apply HrecA.
apply extEqualRefl.
apply H3.
intros.
split.
intros.
unfold composeSigmaFormula in H4.
assert (In v (freeVarFormula LNN (andH (FormulasToFormula n w m A) (subAllFormula LNN B (fun x : nat => match x with | O => var 0 | S x' => var (S x' + w) end))))).
eapply freeVarAddExists1.
apply H4.
simpl in H5.
induction (in_app_or _ _ _ H5).
assert (m + S w <= v \/ v < S w).
eapply freeVarAddExists2.
apply H4.
clear H5 H4 H3 H1 g B.
induction A as [| a n0 A HrecA].
simpl in H6.
decompose sum H6.
rewrite <- H1.
apply le_O_n.
rewrite <- H3.
apply le_O_n.
simpl in H6.
induction (in_app_or _ _ _ H6).
simpl in H2.
induction H2 as (H2, H3).
induction (freeVarSubFormula3 _ _ _ _ _ H1).
apply H2.
eapply In_list_remove1.
apply H4.
induction H4 as [H4| H4].
rewrite <- H4 in H7.
induction H7 as [H5| H5].
rewrite <- plus_Snm_nSm in H5.
simpl in H5.
elim (le_Sn_n _ H5).
elim (lt_not_le _ _ H5).
apply le_n_S.
apply le_plus_r.
elim H4.
apply HrecA; auto.
simpl in H2.
tauto.
induction H7 as [H3| H3].
left.
simpl in H3.
eapply le_trans.
apply le_n_Sn.
apply H3.
auto.
decompose record (freeVarSubAllFormula1 _ _ _ _ H6).
destruct x as [| n0].
induction H9 as [H7| H7].
rewrite <- H7.
apply le_O_n.
elim H7.
induction H9 as [H7| H7].
rewrite <- H7.
induction H3 as (H3, H9).
assert (S n0 <= m).
apply H3.
auto.
induction (freeVarAddExists2 _ _ _ _ H4).
rewrite <- H7 in H11.
rewrite <- plus_Snm_nSm in H11.
simpl in H11.
elim (le_not_lt m n0).
apply (fun p n m : nat => plus_le_reg_l n m p) with w.
repeat rewrite (plus_comm w).
apply le_S_n.
auto.
apply lt_S_n.
apply le_lt_n_Sm.
auto.
rewrite <- H7 in H11.
elim (lt_not_le _ _ H11).
apply le_n_S.
apply le_plus_r.
elim H7.
apply H; auto.
Remark boundedCheck : forall P : nat -> Prop, (forall x : nat, decidable (P x)) -> forall c : nat, (forall d : nat, d < c -> ~ P d) \/ (exists d : nat, d < c /\ P d).
Proof.
intros.
induction c as [| c Hrecc]; intros.
left; intros.
elim (lt_n_O _ H0).
induction (H c).
right.
exists c.
split.
apply lt_n_Sn.
auto.
induction Hrecc as [H1| H1].
left.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H2)).
apply H1.
auto.
rewrite H3.
auto.
induction H1 as (x, H1).
right.
exists x.
split.
apply lt_S.
tauto.
tauto.
Remark smallestExists : forall P : nat -> Prop, (forall x : nat, decidable (P x)) -> forall c : nat, P c -> exists a : nat, P a /\ (forall b : nat, b < a -> ~ P b).
Proof.
assert (forall P : nat -> Prop, (forall x : nat, decidable (P x)) -> forall d c : nat, c < d -> P c -> exists a : nat, P a /\ (forall b : nat, b < a -> ~ P b)).
intros P H d.
induction d as [| d Hrecd].
intros.
elim (lt_n_O _ H0).
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H0)).
apply (Hrecd c); auto.
induction (boundedCheck P H c).
exists c.
tauto.
induction H3 as (x, H3).
apply (Hrecd x).
rewrite <- H2.
tauto.
tauto.
intros.
eapply H.
apply H0.
apply lt_n_Sn.
apply H1.
Let minimize (A B : Formula) (v x : nat) : Formula := andH A (forallH x (impH (LT (var x) (var v)) (notH (substituteFormula LNN B v (var x))))).
Remark minimize1 : forall (A B : Formula) (v x : nat), v <> x -> ~ In x (freeVarFormula LNN B) -> forall a : nat, SysPrf NN (substituteFormula LNN A v (natToTerm a)) -> SysPrf NN (substituteFormula LNN B v (natToTerm a)) -> (forall b : nat, b < a -> SysPrf NN (notH (substituteFormula LNN A v (natToTerm b)))) -> (forall b : nat, b < a -> SysPrf NN (notH (substituteFormula LNN B v (natToTerm b)))) -> SysPrf NN (iffH (minimize A B v x) (equal (var v) (natToTerm a))).
Proof.
intros.
apply iffI.
unfold minimize in |- *.
apply impI.
apply impE with (substituteFormula LNN (impH (LT (var x) (var v)) (notH (substituteFormula LNN B v (var x)))) x (natToTerm a)).
rewrite (subFormulaImp LNN).
rewrite (subFormulaNot LNN).
apply impTrans with (impH (LT (natToTerm a) (var v)) (notH (substituteFormula LNN B v (natToTerm a)))).
apply iffE1.
apply (reduceImp LNN).
unfold LT at 2 in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
induction (eq_nat_dec x x).
induction (eq_nat_dec x v).
elim H.
auto.
apply iffRefl.
elim b.
auto.
apply (reduceNot LNN).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
elim H0.
eapply In_list_remove1.
apply H5.
apply impTrans with (notH (LT (natToTerm a) (var v))).
apply impI.
apply impE with (notH (notH (substituteFormula LNN B v (natToTerm a)))).
apply cp2.
apply Axm; right; constructor.
apply nnI.
do 2 apply sysWeaken.
auto.
apply impE with (notH (LT (var v) (natToTerm a))).
apply orE with (LT (var v) (natToTerm a)) (orH (equal (var v) (natToTerm a)) (LT (natToTerm a) (var v))).
apply sysWeaken.
apply nn9.
repeat apply impI.
apply contradiction with (LT (var v) (natToTerm a)).
apply Axm; left; left; right; constructor.
apply Axm; left; right; constructor.
apply impI.
apply orSys; repeat apply impI.
apply Axm; left; left; right; constructor.
apply contradiction with (LT (natToTerm a) (var v)).
apply Axm; left; left; right; constructor.
apply Axm; right; constructor.
apply impE with (notH (notH A)).
apply cp2.
apply sysWeaken.
apply boundedLT.
intros.
rewrite (subFormulaNot LNN).
auto.
apply nnI.
eapply andE1.
apply Axm; right; constructor.
apply forallE.
eapply andE2.
apply Axm; right; constructor.
apply impI.
unfold minimize in |- *.
rewrite <- (subFormulaId LNN (andH A (forallH x (impH (LT (var x) (var v)) (notH (substituteFormula LNN B v (var x)))))) v) .
apply impE with (substituteFormula LNN (andH A (forallH x (impH (LT (var x) (var v)) (notH (substituteFormula LNN B v (var x)))))) v (natToTerm a)).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
rewrite (subFormulaAnd LNN).
apply andI.
auto.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec x v).
elim H.
auto.
induction (In_dec eq_nat_dec x (freeVarTerm LNN (natToTerm a))).
elim (closedNatToTerm _ _ a0).
apply forallI.
apply closedNN.
rewrite (subFormulaImp LNN).
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
simpl in |- *.
induction (eq_nat_dec v v).
induction (eq_nat_dec v x).
elim H.
auto.
apply impI.
apply forallE.
apply forallI.
unfold not in |- *; intros.
induction H5 as (x0, H5); induction H5 as (H5, H6).
induction H6 as [x0 H6| x0 H6].
elim closedNN with v.
exists x0; auto.
induction H6.
induction H5 as [H5| H5].
elim b.
auto.
fold (freeVarTerm LNN (natToTerm a)) in H5.
simpl in H5.
rewrite <- app_nil_end in H5.
elim (closedNatToTerm _ _ H5).
apply impE with (LT (var x) (natToTerm a)).
apply sysWeaken.
apply boundedLT.
intros.
rewrite (subFormulaNot LNN).
apply impE with (notH (substituteFormula LNN B v (natToTerm n))).
apply cp2.
apply iffE1.
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
elim H0.
eapply In_list_remove1.
apply H6.
apply H4; auto.
apply Axm; right; constructor.
elim b1.
auto.
Let primRecSigmaFormulaHelp (n : nat) (SigA SigB : Formula) : Formula := andH (existH 0 (andH SigA (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S n)))))) (forallH (S (S (S n))) (impH (LT (var (S (S (S n)))) (var (S n))) (existH 0 (existH (S n) (andH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2 (var (S (S n)))) 0 (var (S n))) (andH (substituteFormula LNN SigB (S (S n)) (var (S (S (S n))))) (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S n)))))) 2 (var (S (S n)))))))))).
Let primRecPiFormulaHelp (n : nat) (SigA SigB : Formula) : Formula := andH (forallH 0 (impH SigA (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S n)))))) (forallH (S (S (S n))) (impH (LT (var (S (S (S n)))) (var (S n))) (forallH 0 (forallH (S n) (impH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2 (var (S (S n)))) 0 (var (S n))) (impH (substituteFormula LNN SigB (S (S n)) (var (S (S (S n))))) (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S n)))))) 2 (var (S (S n)))))))))).
Let primRecSigmaFormula (n : nat) (SigA SigB : Formula) : Formula := existH (S (S n)) (andH (minimize (primRecSigmaFormulaHelp n SigA SigB) (primRecPiFormulaHelp n SigA SigB) (S (S n)) (S (S (S (S n))))) (substituteFormula LNN (substituteFormula LNN betaFormula 2 (var (S (S n)))) 1 (var (S n)))).
Remark notBoundedForall : forall (P : nat -> Prop) (b : nat), (forall x : nat, decidable (P x)) -> ~ (forall n : nat, n < b -> P n) -> exists n : nat, n < b /\ ~ P n.
Proof.
intros.
induction b as [| b Hrecb].
elim H0.
intros.
elim (lt_n_O _ H1).
induction (H b).
assert (~ (forall n : nat, n < b -> P n)).
unfold not in |- *; intros.
elim H0.
intros.
induction (le_lt_or_eq _ _ (lt_n_Sm_le _ _ H3)).
auto.
rewrite H4; auto.
decompose record (Hrecb H2).
exists x.
split.
apply lt_S.
auto.
auto.
exists b.
split.
apply lt_n_Sn.
auto.
Remark In_betaFormula_subst_1_2_0 : forall (a b c : Term) (v : nat), In v (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 a) 2 b) 0 c)) -> In v (freeVarTerm LNN a) \/ In v (freeVarTerm LNN b) \/ In v (freeVarTerm LNN c).
Proof.
intros.
induction (freeVarSubFormula3 _ _ _ _ _ H).
assert (In v (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 a) 2 b))).
eapply In_list_remove1; apply H0.
induction (freeVarSubFormula3 _ _ _ _ _ H1).
assert (In v (freeVarFormula LNN (substituteFormula LNN betaFormula 1 a))).
eapply In_list_remove1; apply H2.
induction (freeVarSubFormula3 _ _ _ _ _ H3).
destruct v as [| n].
elim (In_list_remove2 _ _ _ _ _ H0).
reflexivity.
destruct n.
elim (In_list_remove2 _ _ _ _ _ H4); reflexivity.
destruct n.
elim (In_list_remove2 _ _ _ _ _ H2).
reflexivity.
elim (le_not_lt (S (S (S n))) 2).
assert (Representable 2 beta betaFormula).
apply betaRepresentable.
induction H5 as (H5, H6).
apply H5.
eapply In_list_remove1.
apply H4.
repeat apply lt_n_S.
apply lt_O_Sn.
tauto.
tauto.
tauto.
Remark In_betaFormula_subst_1_2 : forall (a b : Term) (v : nat), In v (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 a) 2 b)) -> In v (freeVarTerm LNN a) \/ In v (freeVarTerm LNN b) \/ In v (freeVarTerm LNN (var 0)).
Proof.
intros.
apply In_betaFormula_subst_1_2_0.
rewrite (subFormulaId LNN).
assumption.
Remark In_betaFormula_subst_1 : forall (a : Term) (v : nat), In v (freeVarFormula LNN (substituteFormula LNN betaFormula 1 a)) -> In v (freeVarTerm LNN a) \/ In v (freeVarTerm LNN (var 2)) \/ In v (freeVarTerm LNN (var 0)).
Proof.
intros.
apply In_betaFormula_subst_1_2.
rewrite (subFormulaId LNN).
assumption.
Remark In_betaFormula : forall v : nat, In v (freeVarFormula LNN betaFormula) -> In v (freeVarTerm LNN (var 1)) \/ In v (freeVarTerm LNN (var 2)) \/ In v (freeVarTerm LNN (var 0)).
Proof.
intros.
apply In_betaFormula_subst_1.
rewrite (subFormulaId LNN).
assumption.
Remark In_betaFormula_subst_2 : forall (a : Term) (v : nat), In v (freeVarFormula LNN (substituteFormula LNN betaFormula 2 a)) -> In v (freeVarTerm LNN a) \/ In v (freeVarTerm LNN (var 1)) \/ In v (freeVarTerm LNN (var 0)).
Proof.
intros.
rewrite <- (subFormulaId LNN betaFormula 1) in H.
decompose sum (In_betaFormula_subst_1_2 _ _ _ H); tauto.
Remark In_betaFormula_subst_2_1 : forall (a b : Term) (v : nat), In v (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 a) 1 b)) -> In v (freeVarTerm LNN a) \/ In v (freeVarTerm LNN b) \/ In v (freeVarTerm LNN (var 0)).
Proof.
intros.
induction (freeVarSubFormula3 _ _ _ _ _ H).
assert (In v (freeVarFormula LNN (substituteFormula LNN betaFormula 2 a))).
eapply In_list_remove1.
apply H0.
decompose sum (In_betaFormula_subst_2 _ _ H1); try tauto.
induction H3 as [H2| H2].
elim (In_list_remove2 _ _ _ _ _ H0).
symmetry in |- *; assumption.
elim H2.
tauto.
Ltac PRsolveFV A B n := unfold existH, forallH, not in |- *; intros; repeat match goal with | H:(_ = _) |- _ => discriminate H | H:(?X1 <> ?X1) |- _ => elim H; reflexivity | H:(?X1 = S ?X1) |- _ => elim (n_Sn _ H) | H:(S ?X1 = ?X1) |- _ => elim (n_Sn X1); symmetry in |- *; apply H | H:(?X1 = S (S ?X1)) |- _ => elim (n_SSn _ H) | H:(S (S ?X1) = ?X1) |- _ => elim (n_SSn X1); symmetry in |- *; apply H | H:(?X1 = S (S (S ?X1))) |- _ => elim (n_SSSn _ H) | H:(S (S (S ?X1)) = ?X1) |- _ => elim (n_SSSn X1); symmetry in |- *; apply H | H:(In ?X3 (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 _) 2 _) 0 _))) |- _ => decompose sum (In_betaFormula_subst_1_2_0 _ _ _ _ H); clear H | H:(In ?X3 (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 _) 2 _))) |- _ => decompose sum (In_betaFormula_subst_1_2 _ _ _ H); clear H | H:(In ?X3 (freeVarFormula LNN (substituteFormula LNN betaFormula 1 _))) |- _ => decompose sum (In_betaFormula_subst_1 _ _ H); clear H | H:(In ?X3 (freeVarFormula LNN betaFormula)) |- _ => decompose sum (In_betaFormula _ H); clear H | H:(In ?X3 (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 _) 1 _))) |- _ => decompose sum (In_betaFormula_subst_2_1 _ _ _ H); clear H | H:(In ?X3 (freeVarFormula LNN (substituteFormula LNN betaFormula 2 _))) |- _ => decompose sum (In_betaFormula_subst_2 _ _ H); clear H (* Match Context With *) | H:(In ?X3 (freeVarFormula LNN (fol.existH LNN ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula LNN X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.forallH LNN ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula LNN X2))); [ apply H | clear H ] | (* . *) H:(In ?X3 (list_remove nat eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X2)); [ eapply In_list_remove1; apply H | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ] | H:(In ?X3 (freeVarFormula LNN (fol.andH LNN ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.impH LNN ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.notH LNN ?X1))) |- _ => assert (In X3 (freeVarFormula LNN X1)); [ apply H | clear H ] | H:(In _ (freeVarFormula LNN (primRecPiFormulaHelp _ _ _))) |- _ => decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H); clear H | J:(In ?X3 (freeVarFormula LNN A)),H:(forall v : nat, In v (freeVarFormula LNN A) -> v <= S n) |- _ => elim (le_not_lt X3 (S n)); [ apply H; apply J | clear J; repeat apply lt_n_Sn || apply lt_S ] | H:(In ?X3 (freeVarFormula LNN B)),H0:(forall v : nat, In v (freeVarFormula LNN B) -> v <= S (S (S n))) |- _ => elim (le_not_lt X3 (S (S (S n)))); [ apply H0; apply H | clear H; repeat apply lt_n_Sn || apply lt_S ] | H:(In _ (_ ++ _)) |- _ => induction (in_app_or _ _ _ H); clear H | H:(In _ (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ => induction (freeVarSubFormula3 _ _ _ _ _ H); clear H | H:(In _ (freeVarFormula LNN (LT ?X1 ?X2))) |- _ => rewrite freeVarLT in H | H:(In _ (freeVarTerm LNN (natToTerm _))) |- _ => elim (closedNatToTerm _ _ H) | H:(In _ (freeVarTerm LNN Zero)) |- _ => elim H | H:(In _ (freeVarTerm LNN (Succ _))) |- _ => rewrite freeVarSucc in H | H:(In _ (freeVarTerm LNN (var _))) |- _ => simpl in H; decompose sum H; clear H | H:(In _ (freeVarTerm LNN (fol.var LNN _))) |- _ => simpl in H; decompose sum H; clear H end.
Remark primRecSigmaRepresentable : forall (n : nat) (A : Formula) (g : naryFunc n), Representable n g A -> forall (B : Formula) (h : naryFunc (S (S n))), Representable (S (S n)) h B -> Representable (S n) (evalPrimRecFunc n g h) (primRecSigmaFormula n A B).
Proof.
assert (forall (n : nat) (A : Formula) (g : naryFunc n), Representable n g A -> forall (B : Formula) (h : naryFunc (S (S n))), Representable (S (S n)) h B -> RepresentableHelp (S n) (evalPrimRecFunc n g h) (primRecSigmaFormula n A B)).
intro.
induction n as [| n Hrecn].
simpl in |- *; intros.
unfold primRecSigmaFormula in |- *.
rewrite (subFormulaExist LNN).
induction (In_dec eq_nat_dec 2 (freeVarTerm LNN (natToTerm a))).
elim (closedNatToTerm _ _ a0).
simpl in |- *.
clear b.
assert (repBeta : Representable 2 beta betaFormula).
apply betaRepresentable.
rewrite (subFormulaAnd LNN).
repeat rewrite (subFormulaId LNN).
apply iffTrans with (fol.existH LNN 2 (fol.andH LNN (minimize (substituteFormula LNN (primRecSigmaFormulaHelp 0 A B) 1 (natToTerm a)) (substituteFormula LNN (primRecPiFormulaHelp 0 A B) 1 (natToTerm a)) 2 4) (substituteFormula LNN betaFormula 1 (natToTerm a)))).
apply (reduceExist LNN).
apply closedNN.
apply (reduceAnd LNN).
apply subFormulaMinimize; first [ discriminate | apply closedNatToTerm ].
apply iffRefl.
set (f := evalPrimRecFunc 0 g h) in *.
induction (betaTheorem1 (S a) f).
induction x as (a0, b).
simpl in p.
set (P := fun c : nat => forall z : nat, z < S a -> f z = beta c z) in *.
assert (forall c : nat, decidable (P c)).
intros.
unfold decidable in |- *.
unfold P in |- *.
set (Q := fun z : nat => f z <> beta c z) in *.
assert (forall z : nat, decidable (Q z)).
intros.
unfold decidable, Q in |- *.
induction (eq_nat_dec (f z) (beta c z)); auto.
induction (boundedCheck Q H1 (S a)).
left.
unfold Q in H2.
intros.
induction (eq_nat_dec (f z) (beta c z)).
auto.
elim (H2 z); auto.
right.
unfold not in |- *; intros.
induction H2 as (x, H2).
induction H2 as (H2, H4).
elim H4.
apply H3; auto.
induction (smallestExists P H1 (cPair b a0)).
induction H2 as (H2, H3).
clear H1 p b a0.
apply iffTrans with (fol.existH LNN 2 (fol.andH LNN (equal (var 2) (natToTerm x)) (substituteFormula LNN betaFormula 1 (natToTerm a)))).
apply (reduceExist LNN).
apply closedNN.
apply (reduceAnd LNN).
assert (subExistSpecial : forall (F : Formula) (a b c : nat), b <> c -> substituteFormula LNN (existH b F) c (natToTerm a) = existH b (substituteFormula LNN F c (natToTerm a))).
intros.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec b c).
elim H1.
auto.
induction (In_dec eq_nat_dec b (freeVarTerm LNN (natToTerm a0))).
elim (closedNatToTerm _ _ a1).
reflexivity.
assert (subForallSpecial : forall (F : Formula) (a b c : nat), b <> c -> substituteFormula LNN (forallH b F) c (natToTerm a) = forallH b (substituteFormula LNN F c (natToTerm a))).
intros.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec b c).
elim H1.
auto.
induction (In_dec eq_nat_dec b (freeVarTerm LNN (natToTerm a0))).
elim (closedNatToTerm _ _ a1).
reflexivity.
apply minimize1.
discriminate.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H1).
assert (In 4 (freeVarFormula LNN (primRecPiFormulaHelp 0 A B))).
eapply In_list_remove1.
apply H4.
decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H5).
induction H as (H, H7).
elim (le_not_lt 4 0).
apply H.
apply H6.
repeat constructor.
induction H0 as (H0, H6).
elim (le_not_lt 4 2).
apply H0.
apply H7.
repeat constructor.
discriminate H6.
discriminate H6.
elim (closedNatToTerm _ _ H4).
unfold primRecSigmaFormulaHelp in |- *.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
rewrite (subFormulaExist LNN).
simpl in |- *.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply andI.
apply existI with (natToTerm (f 0)).
rewrite (subFormulaAnd LNN).
apply andI.
unfold f, evalPrimRecFunc in |- *.
induction H as (H, H1).
simpl in H1.
apply impE with (substituteFormula LNN A 0 (natToTerm g)).
apply iffE2.
apply (reduceSub LNN).
apply closedNN.
apply iffTrans with (substituteFormula LNN A 2 (natToTerm x)).
apply (reduceSub LNN).
apply closedNN.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
elim (le_not_lt 1 0).
apply H; auto.
auto.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
elim (le_not_lt 2 0).
apply H; auto.
auto.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm g)) 0 (natToTerm g)).
apply iffE2.
apply (reduceSub LNN).
apply closedNN.
auto.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite (subTermNil LNN).
apply eqRefl.
apply closedNatToTerm.
induction repBeta as (H1, H4).
simpl in H4.
rewrite (subFormulaId LNN).
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (natToTerm x)) 0 (natToTerm (f 0))).
apply iffE2.
apply (reduceSub LNN).
apply closedNN.
apply (reduceSub LNN).
apply closedNN.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (In_list_remove2 _ _ _ _ _ H6).
reflexivity.
elim H6.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm (beta x 0))) 0 (natToTerm (f 0))).
apply iffE2.
apply (reduceSub LNN).
apply closedNN.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (natToTerm 0)).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
apply H4.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite (subTermNil LNN).
rewrite H2.
apply eqRefl.
apply lt_O_Sn.
apply closedNatToTerm.
apply forallI.
apply closedNN.
apply impTrans with (LT (var 3) (natToTerm a)).
unfold LT at 1 in |- *.
repeat rewrite (subFormulaRelation LNN).
simpl in |- *.
rewrite (subTermNil LNN).
apply impRefl.
apply closedNatToTerm.
apply boundedLT.
intros.
repeat rewrite (subFormulaId LNN).
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply existI with (natToTerm (f (S n))).
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply existI with (natToTerm (f n)).
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply andI.
induction repBeta as (H4, H5).
simpl in H5.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm x)) 0 (var 1)) 3 (natToTerm n)) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
unfold not in |- *; intros.
induction H6 as [H6| H6].
discriminate H6.
elim H6.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm x)) 3 (natToTerm n)) 0 (var 1)) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
unfold not in |- *; intros.
induction H6 as [H6| H6].
discriminate H6.
elim H6.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm x)) 3 (natToTerm n)) 0 (var 1)) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H6).
elim (In_list_remove2 _ _ _ _ _ H7).
reflexivity.
induction H7 as [H7| H7].
discriminate H7.
elim H7.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (var 3)) 3 (natToTerm n)) 0 (var 1)) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H6 as [H6| H6].
discriminate H6.
elim H6.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (natToTerm n)) 0 (var 1)) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In 3 (freeVarFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)))).
eapply In_list_remove1.
apply H6.
induction (freeVarSubFormula3 _ _ _ _ _ H7).
elim (le_not_lt 3 2).
apply H4.
eapply In_list_remove1.
apply H8.
repeat constructor.
elim (closedNatToTerm _ _ H8).
apply impE with (substituteFormula LNN (substituteFormula LNN (equal (var 0) (natToTerm (beta x n))) 0 (var 1)) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H5.
repeat rewrite (subFormulaEqual LNN).
simpl in |- *.
repeat rewrite (subTermNil LNN (natToTerm (beta x n))).
rewrite H2.
apply eqRefl.
apply lt_S.
apply H1.
apply closedNatToTerm.
apply closedNatToTerm.
apply andI.
induction H0 as (H0, H4).
simpl in H4.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 3 (natToTerm n)) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (In_list_remove2 _ _ _ _ _ H6).
reflexivity.
induction H6 as [H6| H6].
discriminate H6.
elim H6.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm n)) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
elim (le_not_lt 3 2).
apply H0.
eapply In_list_remove1.
apply H5.
repeat constructor.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm n)) 1 (natToTerm (f n))) 0 (natToTerm (f (S n)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm (h n (f n)))) 0 (natToTerm (f (S n)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H4.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite (subTermNil LNN).
unfold f in |- *.
simpl in |- *.
apply eqRefl.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (Succ (var 3))) 3 (natToTerm n)) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
simpl in |- *; unfold not in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 3 (natToTerm n)) 1 (natToTerm (S n))) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
replace (natToTerm (S n)) with (substituteTerm LNN (Succ (var 3)) 3 (natToTerm n)).
apply (subSubFormula LNN).
discriminate.
apply closedNatToTerm.
simpl in |- *.
reflexivity.
induction repBeta as (H4, H5).
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (natToTerm (S n))) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H6).
elim (le_not_lt 3 2).
apply H4.
eapply In_list_remove1.
apply H7.
repeat constructor.
elim (closedNatToTerm _ _ H7).
simpl in H5.
apply impE with (substituteFormula LNN (substituteFormula LNN (equal (var 0) (natToTerm (beta x (S n)))) 0 (natToTerm (f (S n)))) 1 (natToTerm (f n))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H5.
repeat rewrite (subFormulaEqual LNN).
simpl in |- *.
repeat (rewrite (subTermNil LNN (natToTerm (beta x (S n)))); [ idtac | apply closedNatToTerm ]).
rewrite (subTermNil LNN).
rewrite H2.
apply eqRefl.
apply lt_n_S.
apply H1.
apply closedNatToTerm.
unfold primRecPiFormulaHelp in |- *.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
rewrite (subFormulaForall LNN).
simpl in |- *.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply andI.
apply forallI.
apply closedNN.
induction H as (H, H1).
simpl in H1.
apply impTrans with (substituteFormula LNN (substituteFormula LNN (equal (var 0) (natToTerm g)) 1 (natToTerm a)) 2 (natToTerm x)).
apply iffE1.
apply (reduceSub LNN).
apply closedNN.
apply (reduceSub LNN).
apply closedNN.
apply H1.
repeat rewrite (subFormulaEqual LNN).
simpl in |- *.
repeat (rewrite (subTermNil LNN (natToTerm g)); [ idtac | apply closedNatToTerm ]).
apply impI.
rewrite <- (subFormulaId LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var 2)) 1 (natToTerm a)) 2 (natToTerm x)) 0) .
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var 2)) 1 (natToTerm a)) 2 (natToTerm x)) 0 (natToTerm g)).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
clear H1.
induction repBeta as (H1, H4).
simpl in H4.
rewrite (subFormulaId LNN).
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (natToTerm x)) 0 (natToTerm (f 0))).
apply iffE2.
apply (reduceSub LNN).
apply closedNN.
apply (reduceSub LNN).
apply closedNN.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (In_list_remove2 _ _ _ _ _ H6).
reflexivity.
elim H6.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm (beta x 0))) 0 (natToTerm (f 0))).
apply iffE2.
apply (reduceSub LNN).
apply closedNN.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (natToTerm 0)).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
apply H4.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite (subTermNil LNN).
rewrite H2.
apply eqRefl.
apply lt_O_Sn.
apply closedNatToTerm.
apply forallI.
apply closedNN.
apply impTrans with (LT (var 3) (natToTerm a)).
unfold LT at 1 in |- *.
repeat rewrite (subFormulaRelation LNN).
simpl in |- *.
rewrite (subTermNil LNN).
apply impRefl.
apply closedNatToTerm.
apply boundedLT.
intros.
repeat rewrite (subFormulaId LNN).
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply forallI.
apply closedNN.
apply forallI.
apply closedNN.
apply impTrans with (equal (var 1) (natToTerm (f n))).
induction repBeta as (H4, H5).
simpl in H5.
apply impTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm x)) 0 (var 1)) 3 (natToTerm n)).
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H6 as [H6| H6].
discriminate H6.
elim H6.
apply closedNatToTerm.
apply impTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm x)) 3 (natToTerm n)) 0 (var 1)).
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H6 as [H6| H6].
discriminate H6.
elim H6.
apply closedNatToTerm.
apply impTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (var 3)) 3 (natToTerm n)) 0 (var 1)).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
unfold not in |- *; intros.
induction H6 as [H6| H6].
discriminate H6.
elim H6.
apply impTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (natToTerm n)) 0 (var 1)).
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In 3 (freeVarFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)))).
eapply In_list_remove1.
apply H6.
induction (freeVarSubFormula3 _ _ _ _ _ H7).
elim (le_not_lt 3 2).
apply H4.
eapply In_list_remove1.
apply H8.
repeat constructor.
elim (closedNatToTerm _ _ H8).
apply impTrans with (substituteFormula LNN (equal (var 0) (natToTerm (beta x n))) 0 (var 1)).
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H5.
repeat rewrite (subFormulaEqual LNN).
simpl in |- *.
repeat rewrite (subTermNil LNN (natToTerm (beta x n))).
rewrite H2.
apply impRefl.
apply lt_S.
apply H1.
apply closedNatToTerm.
rewrite <- (subFormulaId LNN (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm x)) 3 (natToTerm n)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (natToTerm x)) 3 (natToTerm n))) 1).
apply impI.
apply impE with (substituteFormula LNN (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm x)) 3 (natToTerm n)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (natToTerm x)) 3 (natToTerm n))) 1 (natToTerm (f n))).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
rewrite (subFormulaImp LNN).
apply impTrans with (equal (var 0) (natToTerm (f (S n)))).
induction H0 as (H0, H4).
simpl in H4.
apply impTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 3 (natToTerm n)) 1 (natToTerm (f n))).
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (In_list_remove2 _ _ _ _ _ H6).
reflexivity.
induction H6 as [H6| H6].
discriminate H6.
elim H6.
apply impTrans with (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm n)) 1 (natToTerm (f n))).
apply iffE1.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
elim (le_not_lt 3 2).
apply H0.
eapply In_list_remove1.
apply H5.
repeat constructor.
unfold f in |- *.
simpl in |- *.
apply iffE1.
apply H4.
rewrite <- (subFormulaId LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (natToTerm x)) 3 (natToTerm n)) 1 (natToTerm (f n))) 0) .
apply impI.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (natToTerm x)) 3 (natToTerm n)) 1 (natToTerm (f n))) 0 (natToTerm (f (S n)))).
apply (subWithEquals LNN).
apply eqSym.
apply Axm; right; constructor.
apply sysWeaken.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (Succ (var 3))) 3 (natToTerm n)) 1 (natToTerm (f n))) 0 (natToTerm (f (S n)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
simpl in |- *; unfold not in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 3 (natToTerm n)) 1 (natToTerm (S n))) 1 (natToTerm (f n))) 0 (natToTerm (f (S n)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
replace (natToTerm (S n)) with (substituteTerm LNN (Succ (var 3)) 3 (natToTerm n)).
apply (subSubFormula LNN).
discriminate.
apply closedNatToTerm.
simpl in |- *.
reflexivity.
induction repBeta as (H4, H5).
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (natToTerm (S n))) 1 (natToTerm (f n))) 0 (natToTerm (f (S n)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H6).
elim (le_not_lt 3 2).
apply H4.
eapply In_list_remove1.
apply H7.
repeat constructor.
elim (closedNatToTerm _ _ H7).
simpl in H5.
apply impE with (substituteFormula LNN (substituteFormula LNN (equal (var 0) (natToTerm (beta x (S n)))) 1 (natToTerm (f n))) 0 (natToTerm (f (S n)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H5.
repeat rewrite (subFormulaEqual LNN).
simpl in |- *.
repeat (rewrite (subTermNil LNN (natToTerm (beta x (S n)))); [ idtac | apply closedNatToTerm ]).
rewrite H2.
apply eqRefl.
apply lt_n_S.
apply H1.
intros.
assert (forall z : nat, decidable (f z = beta b z)).
unfold decidable in |- *.
intros.
induction (eq_nat_dec (f z) (beta b z)); auto.
decompose record (notBoundedForall (fun z : nat => f z = beta b z) (S a) H4 (H3 b H1)).
apply impE with (notH (equal (natToTerm (f x0)) (natToTerm (beta b x0)))).
apply cp2.
unfold primRecSigmaFormulaHelp in |- *.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
rewrite (subFormulaExist LNN).
simpl in |- *.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply impI.
clear H4 H1 H3 H2 x P.
clear H7.
induction x0 as [| x0 Hrecx0].
apply impE with (existH 0 (fol.andH LNN (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2 (natToTerm b)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var 2)) 1 (natToTerm a)) 2 (natToTerm b)))).
apply sysWeaken.
apply impI.
apply existSys.
apply closedNN.
unfold not in |- *; simpl in |- *; intros.
induction (in_app_or _ _ _ H1).
elim (closedNatToTerm _ _ H2).
elim (closedNatToTerm _ _ H2).
apply eqTrans with (var 0).
induction H as (H, H1).
simpl in H1.
apply eqSym.
unfold f in |- *; simpl in |- *.
apply impE with A.
apply sysWeaken.
apply iffE1.
assumption.
apply impE with (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2 (natToTerm b)).
apply sysWeaken.
apply iffE1.
apply iffTrans with (substituteFormula LNN A 2 (natToTerm b)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
elim (le_not_lt 1 0); auto.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
elim (le_not_lt 2 0); auto.
eapply andE1.
apply Axm; right; constructor.
induction repBeta as (H1, H2).
simpl in H2.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var 2)) 1 (natToTerm a)) 2 (natToTerm b)).
apply sysWeaken.
apply iffE1.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (natToTerm 0)).
rewrite (subFormulaId LNN).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (natToTerm b)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H3).
elim (In_list_remove2 _ _ _ _ _ H4); reflexivity.
apply H4.
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
apply H2.
eapply andE2.
apply Axm; right; constructor.
eapply andE1.
apply Axm; right; constructor.
apply impE with (equal (natToTerm (f x0)) (natToTerm (beta b x0))); [ idtac | apply Hrecx0 ].
clear Hrecx0.
apply impE with (forallH 3 (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2 (natToTerm b)) (existH 0 (existH 1 (fol.andH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) (fol.andH LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)))))))); [ idtac | eapply andE2; apply Axm; right; constructor ].
apply sysWeaken.
apply impTrans with (substituteFormula LNN (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2 (natToTerm b)) (existH 0 (existH 1 (fol.andH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) (fol.andH LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b))))))) 3 (natToTerm x0)).
apply impI.
apply forallE.
apply Axm; right; constructor.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply impTrans with (existH 0 (existH 1 (fol.andH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) 3 (natToTerm x0)) (fol.andH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)))))).
apply impI.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2 (natToTerm b)) 3 (natToTerm x0)).
apply Axm; right; constructor.
apply sysWeaken.
unfold LT in |- *.
repeat rewrite (subFormulaRelation LNN).
simpl in |- *.
repeat (rewrite (subTermNil LNN (natToTerm a)); [ idtac | apply closedNatToTerm ]).
fold (LT (natToTerm x0) (natToTerm a)) in |- *.
apply natLT.
apply lt_S_n.
assumption.
apply impI.
assert (forall n : nat, ~ In n (freeVarFormula LNN (impH (equal (natToTerm (f x0)) (natToTerm (beta b x0))) (equal (natToTerm (f (S x0))) (natToTerm (beta b (S x0))))))).
unfold not in |- *; simpl in |- *; intros.
induction (in_app_or _ _ _ H1); induction (in_app_or _ _ _ H2); elim (closedNatToTerm _ _ H3).
apply existSys.
apply closedNN.
apply H1.
apply existSys.
apply closedNN.
apply H1.
unfold f at 2 in |- *; simpl in |- *.
fold (f x0) in |- *.
apply impE with (equal (var 1) (natToTerm (beta b x0))).
apply impI.
apply impE with (equal (var 0) (natToTerm (h x0 (beta b x0)))).
repeat apply impI.
apply eqTrans with (var 0).
apply eqTrans with (natToTerm (h x0 (beta b x0))).
induction (eq_nat_dec (f x0) (beta b x0)).
rewrite a0.
apply eqRefl.
apply contradiction with (equal (natToTerm (f x0)) (natToTerm (beta b x0))).
apply Axm; right; constructor.
do 4 apply sysWeaken.
apply natNE.
auto.
apply eqSym.
apply Axm; left; right; constructor.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)).
do 4 apply sysWeaken.
apply iffE1.
induction repBeta as (H2, H3).
simpl in H3.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (natToTerm (S x0))).
rewrite (subFormulaId LNN).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (Succ (var 3))) 3 (natToTerm x0)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; simpl in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 3 (natToTerm x0)) 1 (substituteTerm LNN (Succ (var 3)) 3 (natToTerm x0))).
apply (subSubFormula LNN).
discriminate.
apply closedNatToTerm.
simpl in |- *.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (substituteTerm LNN (Succ (var 3)) 3 (natToTerm x0))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
elim (le_not_lt 3 2).
apply H2.
eapply In_list_remove1.
apply H5.
repeat constructor.
elim (closedNatToTerm _ _ H5).
apply iffRefl.
apply H3.
eapply andE2.
eapply andE2.
apply Axm; do 3 left; right; constructor.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) 1 (natToTerm (beta b x0))).
do 2 apply sysWeaken.
induction H0 as (H0, H2).
simpl in H2.
apply iffE1.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm x0)) 1 (natToTerm (beta b x0))).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 3 (natToTerm x0)) 1 (natToTerm (beta b x0))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H3).
elim (In_list_remove2 _ _ _ _ _ H4).
reflexivity.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
elim (le_not_lt 3 2).
apply H0.
eapply In_list_remove1.
apply H3.
repeat constructor.
apply H2.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) 1 (var 1)).
apply (subWithEquals LNN).
apply Axm; right; constructor.
repeat rewrite (subFormulaId LNN).
eapply andE1.
eapply andE2.
apply Axm; left; right; constructor.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) 3 (natToTerm x0)).
apply sysWeaken.
apply iffE1.
induction repBeta as (H2, H3).
simpl in H3.
apply iffTrans with (substituteFormula LNN (equal (var 0) (natToTerm (beta b x0))) 0 (var 1)).
rewrite (subFormulaId LNN).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm b)) 0 (var 1)) 3 (natToTerm x0)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) 0 (var 1)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply (reduceSub LNN).
apply closedNN.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (var 3)) 3 (natToTerm x0)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (natToTerm x0)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In 3 (freeVarFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)))).
eapply In_list_remove1.
apply H4.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (le_not_lt 3 2).
apply H2.
eapply In_list_remove1.
apply H7.
repeat constructor.
elim (closedNatToTerm _ _ H7).
apply H3.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite subTermNil.
apply iffRefl.
apply closedNatToTerm.
eapply andE1.
apply Axm; right; constructor.
apply lt_S.
apply lt_S_n.
assumption.
apply natNE.
auto.
intros.
assert (forall z : nat, decidable (f z = beta b z)).
unfold decidable in |- *.
intros.
induction (eq_nat_dec (f z) (beta b z)); auto.
decompose record (notBoundedForall (fun z : nat => f z = beta b z) (S a) H4 (H3 b H1)).
apply impE with (notH (equal (natToTerm (f x0)) (natToTerm (beta b x0)))).
apply cp2.
unfold primRecPiFormulaHelp in |- *.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
rewrite (subFormulaForall LNN).
simpl in |- *.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply impI.
clear H4 H1 H3 H2 x P.
clear H7.
induction x0 as [| x0 Hrecx0].
apply impE with (forallH 0 (fol.impH LNN (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2 (natToTerm b)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var 2)) 1 (natToTerm a)) 2 (natToTerm b)))).
apply sysWeaken.
apply impTrans with (substituteFormula LNN (fol.impH LNN (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2 (natToTerm b)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var 2)) 1 (natToTerm a)) 2 (natToTerm b))) 0 (natToTerm (f 0))).
apply impI.
apply forallE.
apply Axm; right; constructor.
apply impI.
rewrite (subFormulaImp LNN).
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var 2)) 1 (natToTerm a)) 2 (natToTerm b)) 0 (natToTerm (f 0))).
apply sysWeaken.
apply impTrans with (substituteFormula LNN (equal (var 0) (natToTerm (beta b 0))) 0 (natToTerm (f 0))).
apply iffE1.
apply (reduceSub LNN).
apply closedNN.
rewrite (subFormulaId LNN).
induction repBeta as (H1, H2).
simpl in H2.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (natToTerm 0)).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (natToTerm b)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H3).
elim (In_list_remove2 _ _ _ _ _ H4); reflexivity.
apply H4.
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
apply H2.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite (subTermNil LNN).
apply impRefl.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN A 1 (natToTerm a)) 2 (natToTerm b)) 0 (natToTerm (f 0))).
apply Axm; right; constructor.
apply sysWeaken.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm (f 0))) 0 (natToTerm (f 0))).
apply iffE2.
apply (reduceSub LNN); [ apply closedNN | idtac ].
induction H as (H, H1).
simpl in H1.
unfold f in |- *; simpl in |- *.
apply iffTrans with A; [ idtac | assumption ].
apply iffTrans with (substituteFormula LNN A 2 (natToTerm b)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
elim (le_not_lt 1 0); auto.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
elim (le_not_lt 2 0); auto.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite (subTermNil LNN).
apply eqRefl.
apply closedNatToTerm.
eapply andE1.
apply Axm; right; constructor.
apply impE with (equal (natToTerm (f x0)) (natToTerm (beta b x0))); [ idtac | apply Hrecx0 ].
clear Hrecx0.
apply impE with (forallH 3 (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2 (natToTerm b)) (forallH 0 (forallH 1 (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) (fol.impH LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)))))))); [ idtac | eapply andE2; apply Axm; right; constructor ].
apply sysWeaken.
apply impTrans with (substituteFormula LNN (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2 (natToTerm b)) (forallH 0 (forallH 1 (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) (fol.impH LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b))))))) 3 (natToTerm x0)).
apply impI.
apply forallE.
apply Axm; right; constructor.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply impTrans with (forallH 0 (forallH 1 (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) 3 (natToTerm x0)) (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)))))).
apply impI.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (LT (var 3) (var 1)) 1 (natToTerm a)) 2 (natToTerm b)) 3 (natToTerm x0)).
apply Axm; right; constructor.
apply sysWeaken.
unfold LT in |- *.
repeat rewrite (subFormulaRelation LNN).
simpl in |- *.
repeat (rewrite (subTermNil LNN (natToTerm a)); [ idtac | apply closedNatToTerm ]).
fold (LT (natToTerm x0) (natToTerm a)) in |- *.
apply natLT.
apply lt_S_n.
assumption.
apply impTrans with (substituteFormula LNN (forallH 1 (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) 3 (natToTerm x0)) (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)) 3 (natToTerm x0))))) 0 (natToTerm (f (S x0)))).
apply impI.
apply forallE.
apply Axm; right; constructor.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
apply impTrans with (substituteFormula LNN (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (var 2)) 0 (var 1)) 2 (natToTerm b)) 3 (natToTerm x0)) 0 (natToTerm (f (S x0)))) (fol.impH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) 0 (natToTerm (f (S x0)))) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)) 0 (natToTerm (f (S x0)))))) 1 (natToTerm (beta b x0))).
apply impI.
apply forallE.
apply Axm; right; constructor.
repeat first [ rewrite subExistSpecial; [ idtac | discriminate ] | rewrite subForallSpecial; [ idtac | discriminate ] | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) ].
repeat apply impI.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm (beta b (S x0)))) 0 (natToTerm (f (S x0)))).
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite (subTermNil LNN).
apply impRefl.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)) 0 (natToTerm (f (S x0)))) 1 (natToTerm (beta b x0))).
do 2 apply sysWeaken.
apply iffE1.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var 3))) 2 (var 2)) 2 (natToTerm b)) 3 (natToTerm x0)) 1 (natToTerm (beta b x0))) 0 (natToTerm (f (S x0)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
apply (reduceSub LNN).
apply closedNN.
induction H0 as (H0, H1).
induction repBeta as (H2, H3).
simpl in H3.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (natToTerm (S x0))).
rewrite (subFormulaId LNN).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (Succ (var 3))) 3 (natToTerm x0)) 1 (natToTerm (beta b x0))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; simpl in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 3 (natToTerm x0)) 1 (substituteTerm LNN (Succ (var 3)) 3 (natToTerm x0))) 1 (natToTerm (beta b x0))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subSubFormula LNN).
discriminate.
apply closedNatToTerm.
simpl in |- *.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (substituteTerm LNN (Succ (var 3)) 3 (natToTerm x0))) 1 (natToTerm (beta b x0))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
elim (le_not_lt 3 2).
apply H2.
eapply In_list_remove1.
apply H5.
repeat constructor.
elim (closedNatToTerm _ _ H5).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
elim (In_list_remove2 _ _ _ _ _ H5).
reflexivity.
rewrite freeVarSucc in H5.
elim (closedNatToTerm _ _ H5).
apply H3.
eapply impE.
eapply impE.
apply Axm; left; right; constructor.
do 2 apply sysWeaken.
apply impE with (substituteFormula LNN (substituteFormula LNN (equal (var 1) (natToTerm (beta b x0))) 0 (natToTerm (f (S x0)))) 1 (natToTerm (beta b x0))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
induction H0 as (H0, H1).
induction repBeta as (H2, H3).
simpl in H3.
apply iffTrans with (substituteFormula LNN (equal (var 0) (natToTerm (beta b x0))) 0 (var 1)).
rewrite (subFormulaId LNN).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm b)) 0 (var 1)) 3 (natToTerm x0)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) 0 (var 1)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply (reduceSub LNN).
apply closedNN.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (var 3)) 3 (natToTerm x0)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
unfold not in |- *; intros.
induction H4 as [H4| H4].
discriminate H4.
apply H4.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)) 1 (natToTerm x0)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In 3 (freeVarFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm b)))).
eapply In_list_remove1.
apply H4.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (le_not_lt 3 2).
apply H2.
eapply In_list_remove1.
apply H7.
repeat constructor.
elim (closedNatToTerm _ _ H7).
apply H3.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite subTermNil.
apply iffRefl.
apply closedNatToTerm.
repeat rewrite (subFormulaEqual LNN).
simpl in |- *.
repeat rewrite (subTermNil LNN (natToTerm (beta b x0))); try apply closedNatToTerm.
apply eqRefl.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) 0 (natToTerm (f (S x0)))) 1 (natToTerm (f x0))).
apply (subWithEquals LNN).
apply Axm; right; constructor.
do 2 apply sysWeaken.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 2 (natToTerm b)) 3 (natToTerm x0)) 1 (natToTerm (f x0))) 0 (natToTerm (f (S x0)))).
apply iffE1.
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm (f (S x0)))) 0 (natToTerm (f (S x0)))).
apply iffE2.
apply (reduceSub LNN).
apply closedNN.
induction H0 as (H0, H1).
simpl in H1.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm x0)) 1 (natToTerm (f x0))).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (var 3)) 3 (natToTerm x0)) 1 (natToTerm (f x0))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H2).
elim (In_list_remove2 _ _ _ _ _ H3).
reflexivity.
induction H3 as [H3| H3].
discriminate H3.
apply H3.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
elim (le_not_lt 3 2).
apply H0.
eapply In_list_remove1.
apply H2.
repeat constructor.
unfold f in |- *.
simpl in |- *.
apply H1.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite (subTermNil LNN).
apply eqRefl.
apply closedNatToTerm.
apply lt_S.
apply lt_S_n.
assumption.
apply natNE.
auto.
apply iffRefl.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 1 (natToTerm a)) 2 (natToTerm x)).
apply iffI.
apply impI.
apply existSys.
apply closedNN.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H1).
elim (In_list_remove2 _ _ _ _ _ H4).
reflexivity.
elim (closedNatToTerm _ _ H4).
apply impE with (substituteFormula LNN (substituteFormula LNN betaFormula 1 (natToTerm a)) 2 (var 2)).
apply (subWithEquals LNN).
eapply andE1.
apply Axm; right; constructor.
rewrite (subFormulaId LNN).
eapply andE2.
apply Axm; right; constructor.
apply impI.
apply existI with (natToTerm x).
rewrite (subFormulaAnd LNN).
apply andI.
rewrite (subFormulaEqual LNN).
simpl in |- *.
rewrite subTermNil.
apply eqRefl.
apply closedNatToTerm.
apply Axm; right; constructor.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 2 (natToTerm x)) 1 (natToTerm a)).
apply (subFormulaExch LNN).
discriminate.
apply closedNatToTerm.
apply closedNatToTerm.
rewrite H2.
induction repBeta as (H1, H4).
apply H4.
apply lt_n_Sn.
unfold P in |- *; intros.
unfold beta in |- *.
repeat rewrite cPairProjections1.
repeat rewrite cPairProjections2.
apply (p z).
assumption.
simpl in |- *.
intros.
simpl in Hrecn.
apply Representable_ext with (evalPrimRecFunc n (g a0) (fun x y : nat => h x y a0) a).
induction a as [| a Hreca].
simpl in |- *.
apply extEqualRefl.
simpl in |- *.
apply extEqualCompose2.
apply Hreca.
apply extEqualRefl.
induction H as (H, H1).
induction H0 as (H0, H2).
simpl in H1.
simpl in H2.
assert (RepresentableHelp n (evalPrimRecFunc n (g a0) (fun x y : nat => h x y a0) a) (substituteFormula LNN (primRecSigmaFormula n (substituteFormula LNN A (S n) (natToTerm a0)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n))))) (S n) (natToTerm a))).
apply Hrecn.
split.
intros.
induction (freeVarSubFormula3 _ _ _ _ _ H3).
assert (v <= S n).
apply H.
eapply In_list_remove1.
apply H4.
induction (le_lt_or_eq _ _ H5).
apply lt_n_Sm_le.
auto.
elim (In_list_remove2 _ _ _ _ _ H4).
auto.
elim (closedNatToTerm _ _ H4).
apply H1.
split.
intros.
repeat match goal with | H:(In v (list_remove nat eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ => assert (In v (freeVarFormula LNN X2)); [ eapply In_list_remove1; apply H | assert (v <> X1); [ eapply In_list_remove2; apply H | clear H ] ] | H:(In v (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ => induction (freeVarSubFormula3 _ _ _ _ _ H); clear H end.
assert (v <= S (S (S n))).
apply H0.
auto.
induction (le_lt_or_eq _ _ H4).
apply lt_n_Sm_le.
auto.
elim H5; auto.
elim (closedNatToTerm _ _ H4).
induction H4 as [H3| H3].
rewrite <- H3.
apply le_n_Sn.
elim H3.
induction H4 as [H3| H3].
rewrite <- H3.
apply le_n.
elim H3.
simpl in |- *.
intros.
apply RepresentableAlternate with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S (S (S n))) (natToTerm a1)) (S (S n)) (natToTerm a2)) (S n) (natToTerm a0)).
apply iffSym.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (natToTerm a1)) (S n) (natToTerm a2)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
repeat match goal with | H:(In ?X1 (list_remove nat eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ => elim (In_list_remove2 _ _ _ _ _ H); reflexivity | H:(In ?X3 (list_remove nat eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X2)); [ eapply In_list_remove1; apply H | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ] | H:(In ?X4 (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ => induction (freeVarSubFormula3 _ _ _ _ _ H); clear H | H:(In ?X4 (freeVarTerm LNN (var ?X1))) |- _ => induction H as [H3| H3]; [ idtac | contradiction ] end.
elim (le_not_lt (S (S n)) (S n)).
rewrite <- H3.
apply le_n.
apply lt_n_Sn.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S (S n))) (natToTerm a1)) (S (S n)) (var (S n))) (S n) (natToTerm a2)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
unfold not in |- *; intros.
elim (le_not_lt (S (S (S n))) (S (S n))).
rewrite <- H3.
apply le_n.
apply lt_n_Sn.
unfold not in |- *; intros.
simpl in H3.
decompose sum H3.
elim (le_not_lt (S (S (S n))) (S n)).
rewrite <- H4.
apply le_n.
apply lt_S.
apply lt_n_Sn.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S (S n))) (natToTerm a1)) (S (S n)) (natToTerm a2)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
repeat match goal with | H:(In ?X1 (list_remove nat eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ => elim (In_list_remove2 _ _ _ _ _ H); reflexivity | H:(In ?X3 (list_remove nat eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X2)); [ eapply In_list_remove1; apply H | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ] | H:(In ?X4 (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ => induction (freeVarSubFormula3 _ _ _ _ _ H); clear H | H:(In ?X4 (freeVarTerm LNN (var ?X1))) |- _ => simple induction H; [ idtac | contradiction ] end.
elim (closedNatToTerm _ _ H3).
elim (closedNatToTerm _ _ H3).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S (S (S n))) (natToTerm a1)) (S n) (natToTerm a0)) (S (S n)) (natToTerm a2)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
unfold not in |- *; intros.
elim (le_not_lt (S (S (S n))) (S n)).
rewrite <- H3.
apply le_n.
apply lt_S.
apply lt_n_Sn.
apply closedNatToTerm.
apply closedNatToTerm.
apply (subFormulaExch LNN).
unfold not in |- *; intros.
elim (le_not_lt (S (S n)) (S n)).
rewrite <- H3.
apply le_n.
apply lt_n_Sn.
apply closedNatToTerm.
apply closedNatToTerm.
apply H2.
apply RepresentableAlternate with (substituteFormula LNN (primRecSigmaFormula n (substituteFormula LNN A (S n) (natToTerm a0)) (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n))))) (S n) (natToTerm a)).
clear H3 Hrecn.
apply iffSym.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (primRecSigmaFormula (S n) A B) (S n) (natToTerm a0)) (S (S n)) (natToTerm a)).
apply (subFormulaExch LNN).
unfold not in |- *; intros.
elim (le_not_lt (S (S n)) (S n)).
rewrite H3.
apply le_n.
apply lt_n_Sn.
apply closedNatToTerm.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (primRecSigmaFormula (S n) A B) (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S n) (natToTerm a)).
apply iffSym.
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In (S n) (freeVarFormula LNN (substituteFormula LNN (primRecSigmaFormula (S n) A B) (S n) (natToTerm a0)))).
eapply In_list_remove1.
apply H3.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
elim (In_list_remove2 _ _ _ _ _ H5).
reflexivity.
elim (closedNatToTerm _ _ H5).
apply (reduceSub LNN).
apply closedNN.
unfold primRecSigmaFormula in |- *.
assert (H3 := I).
assert (H4 := I).
assert (subExistSpecial : forall (F : Formula) (a b c : nat), b <> c -> substituteFormula LNN (existH b F) c (natToTerm a) = existH b (substituteFormula LNN F c (natToTerm a))).
intros.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec b c).
elim H5.
auto.
induction (In_dec eq_nat_dec b (freeVarTerm LNN (natToTerm a1))).
elim (closedNatToTerm _ _ a2).
reflexivity.
assert (subForallSpecial : forall (F : Formula) (a b c : nat), b <> c -> substituteFormula LNN (forallH b F) c (natToTerm a) = forallH b (substituteFormula LNN F c (natToTerm a))).
intros.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec b c).
elim H5.
auto.
induction (In_dec eq_nat_dec b (freeVarTerm LNN (natToTerm a1))).
elim (closedNatToTerm _ _ a2).
reflexivity.
assert (forall a b : nat, a <> b -> b <> a).
auto.
assert (subExistSpecial2 : forall (F : Formula) (a b c : nat), b <> c -> b <> a -> substituteFormula LNN (existH b F) c (var a) = existH b (substituteFormula LNN F c (var a))).
intros.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec b c).
elim H6.
auto.
induction (In_dec eq_nat_dec b (freeVarTerm LNN (var a1))).
induction a2 as [H8| H8].
elim H7; auto.
elim H8.
reflexivity.
assert (subForallSpecial2 : forall (F : Formula) (a b c : nat), b <> c -> b <> a -> substituteFormula LNN (forallH b F) c (var a) = forallH b (substituteFormula LNN F c (var a))).
intros.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec b c).
elim H6.
auto.
induction (In_dec eq_nat_dec b (freeVarTerm LNN (var a1))).
induction a2 as [H8| H8].
elim H7; auto.
elim H8.
reflexivity.
assert (H6 := I).
assert (H7 := I).
assert (forall (a b : Term) (v : nat) (s : Term), substituteFormula LNN (LT a b) v s = LT (substituteTerm LNN a v s) (substituteTerm LNN b v s)).
intros.
unfold LT in |- *.
rewrite (subFormulaRelation LNN).
reflexivity.
assert (forall (f : Formula) (a : nat) (s : Term), substituteFormula LNN (existH a f) a s = existH a f).
intros.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec a1 a1).
reflexivity.
elim b; auto.
assert (forall (f : Formula) (a : nat) (s : Term), substituteFormula LNN (forallH a f) a s = forallH a f).
intros.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec a1 a1).
reflexivity.
elim b; auto.
assert (H11 := I).
assert (H12 := I).
assert (H13 := I).
assert (H14 := I).
assert (H15 := I).
assert (H16 := I).
Opaque substituteFormula.
unfold minimize, primRecSigmaFormulaHelp, primRecPiFormulaHelp, andH, impH, notH in |- *; repeat first [ discriminate | simple apply iffRefl | simple apply (reduceExist LNN); [ apply closedNN | idtac ] | simple apply (reduceForall LNN); [ apply closedNN | idtac ] | simple apply (reduceAnd LNN) | simple apply (reduceImp LNN) | simple apply (reduceNot LNN) | match goal with | |- (folProof.SysPrf LNN NN (fol.iffH LNN (substituteFormula LNN (substituteFormula LNN (existH (S (S n)) ?X1) ?X2 (var (S (S n)))) ?X3 ?X4) _)) => apply iffTrans with (substituteFormula LNN (substituteFormula LNN (existH (S n) (substituteFormula LNN X1 (S (S n)) (var (S n)))) X2 (var (S (S n)))) X3 X4); [ repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]); apply (rebindExist LNN) | idtac ] | |- (folProof.SysPrf LNN NN (fol.iffH LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (forallH (S (S n)) ?X1) ?X2 (var (S (S n)))) ?X3 ?X4) ?X5 ?X6) _)) => apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (forallH (S n) (substituteFormula LNN X1 (S (S n)) (var (S n)))) X2 (var (S (S n)))) X3 X4) X5 X6); [ repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]); apply (rebindForall LNN) | idtac ] | |- (folProof.SysPrf LNN NN (fol.iffH LNN (substituteFormula LNN (forallH (S ?X6) ?X1) ?X2 (var (S ?X6))) _)) => apply iffTrans with (substituteFormula LNN (forallH X6 (substituteFormula LNN X1 (S X6) (var X6))) X2 (var (S X6))); [ repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]); apply (rebindForall LNN) | idtac ] | |- (folProof.SysPrf LNN NN (fol.iffH LNN (existH (S ?X1) ?X2) ?X3)) => apply iffTrans with (existH X1 (substituteFormula LNN X2 (S X1) (var X1))); [ apply (rebindExist LNN) | idtac ] | |- (folProof.SysPrf LNN NN (fol.iffH LNN (forallH (S ?X1) ?X2) ?X3)) => apply iffTrans with (forallH X1 (substituteFormula LNN X2 (S X1) (var X1))); [ apply (rebindForall LNN) | idtac ] | |- (?X1 <> S ?X1) => apply n_Sn | |- (?X1 <> S (S ?X1)) => apply n_SSn | |- (?X1 <> S (S (S ?X1))) => apply n_SSSn | |- (?X1 <> S (S (S (S ?X1)))) => apply n_SSSSn | |- (S ?X1 <> ?X1) => apply H5; apply n_Sn | |- (S (S ?X1) <> ?X1) => apply H5; apply n_SSn | |- (S (S (S ?X1)) <> ?X1) => apply H5; apply n_SSSn | |- (S (S (S (S ?X1))) <> ?X1) => apply H5; apply n_SSSSn | |- (~ In _ _) => PRsolveFV A B n end | rewrite H9 | rewrite H10 | rewrite (subFormulaAnd LNN) | rewrite (subFormulaImp LNN) | rewrite (subFormulaNot LNN) | rewrite H8 | rewrite (subTermVar1 LNN) | rewrite (subTermVar2 LNN) | rewrite subForallSpecial2; let fail := (match goal with | |- (?X1 <> ?X1) => constr:(false) | _ => constr:(true) end) in match constr:(fail) with | true => idtac end | rewrite subForallSpecial | rewrite subExistSpecial2; let fail := (match goal with | |- (?X1 <> ?X1) => constr:(false) | _ => constr:(true) end) in match constr:(fail) with | true => idtac end | rewrite subExistSpecial ].
apply iffTrans with (substituteFormula LNN (substituteFormula LNN A (S n) (natToTerm a0)) (S (S (S n))) (var (S (S n)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
PRsolveFV A B n.
apply (subFormulaNil LNN).
PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S (S n))))) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S (S n))))) (S (S (S n))) (var (S (S n)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
PRsolveFV A B n.
apply (subFormulaTrans LNN).
PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S n))))) 0 (var (S (S n)))) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S n))))) 0 (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S n))))) (S (S (S n))) (var (S (S n)))) 0 (var (S n))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S n)))) 0 (var (S n))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) 0 (var (S n))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) (S (S (S (S n)))) (var (S (S (S n))))) 2 (var (S (S n)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S (S n))) (var (S (S (S (S n)))))) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S (S (S n)))))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S (S (S n)))))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S (S n))))).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffSym.
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) 2 (var (S (S (S n))))) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) 2 (var (S (S (S n))))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) 2 (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) (S (S (S (S n)))) (var (S (S (S n))))) 2 (var (S (S n)))).
apply (subFormulaExch LNN); PRsolveFV A B n.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula (S (S (S (S n)))) (var (S (S (S n))))) 1 (substituteTerm LNN (Succ (var (S (S (S (S n)))))) (S (S (S (S n)))) (var (S (S (S n)))))).
apply (subSubFormula LNN); PRsolveFV A B n.
replace (substituteTerm LNN (Succ (var (S (S (S (S n)))))) (S (S (S (S n)))) (var (S (S (S n))))) with (Succ (substituteTerm LNN (var (S (S (S (S n))))) (S (S (S (S n)))) (var (S (S (S n)))))).
rewrite (subTermVar1 LNN).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
reflexivity.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN A (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN A (S n) (natToTerm a0)) (S (S (S n))) (var (S (S n)))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN A (S n) (natToTerm a0)) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN A (S n) (natToTerm a0)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffSym.
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S (S (S (S n))))))) (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S (S (S (S n))))))) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
elim (le_not_lt (S (S (S (S (S n))))) (S n)).
rewrite H17.
apply le_n.
do 3 apply lt_S.
apply lt_n_Sn.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S (S (S (S n))))))) (S (S (S n))) (var (S (S n)))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S (S (S (S n))))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 1 Zero) 2 (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffSym.
apply (subFormulaTrans LNN); PRsolveFV A B n.
elim H19; symmetry in |- *; apply H17.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S n))))) (S (S (S n))) (var (S (S (S (S (S n))))))) 0 (var (S (S n)))) (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S (S (S n))))))) 0 (var (S (S n)))) (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S (S (S n))))))) 0 (var (S (S n)))) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
elim (le_not_lt (S (S (S (S (S n))))) (S n)).
rewrite H17.
apply le_n.
do 3 apply lt_S.
apply lt_n_Sn.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S (S (S n))))))) 0 (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S (S (S n))))))) 0 (var (S n))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) 2 (var (S (S (S (S (S n))))))) (S (S (S (S n)))) (var (S (S (S n))))) 0 (var (S n))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S (S n)))))) (S (S (S (S n)))) (var (S (S (S n))))) 2 (var (S (S (S (S (S n))))))) 0 (var (S n))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2 (var (S (S (S (S (S n))))))) 0 (var (S n))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2 (var (S (S (S (S (S n))))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))) 0 (var (S n))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
elim (le_not_lt (S (S (S (S (S n))))) (S n)).
rewrite <- H18.
apply le_n.
do 3 apply lt_S.
apply lt_n_Sn.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2 (var (S (S (S (S n)))))) 0 (var (S n))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffSym.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (var (S (S (S n))))) 2 (var (S (S n)))) (S (S n)) (var (S (S (S (S n)))))) 0 (var (S n))).
apply (subFormulaExch LNN); PRsolveFV A B n.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
elim H19; symmetry in |- *; assumption.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S (S (S n))) (var (S (S (S (S n)))))) (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S (S (S n))) (var (S (S (S (S n)))))) (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S (S n))) (var (S (S (S (S n)))))) (S (S n)) (var (S n))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S (S (S n)))))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S (S n))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
elim (le_not_lt (S (S (S (S (S n))))) (S n)).
rewrite <- H17.
apply le_n.
do 3 apply lt_S.
apply lt_n_Sn.
apply iffSym.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S n)) (var (S (S (S n))))).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) 2 (var (S (S (S (S (S n))))))) (S n) (natToTerm a0)) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) 2 (var (S (S (S (S (S n))))))) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
elim (le_not_lt (S (S (S (S (S n))))) (S n)).
rewrite H17.
apply le_n.
do 3 apply lt_S.
apply lt_n_Sn.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) 2 (var (S (S (S (S (S n))))))) (S (S (S n))) (var (S (S n)))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) 2 (var (S (S (S (S (S n))))))) (S (S (S (S n)))) (var (S (S (S n))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) (S (S (S (S n)))) (var (S (S (S n))))) 2 (var (S (S (S (S (S n))))))) (S (S (S (S (S n))))) (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S (S n))))))) (S (S (S (S n)))) (var (S (S (S n))))) 2 (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula 1 (Succ (var (S (S (S n)))))) 2 (var (S (S (S (S n)))))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN betaFormula (S (S (S (S n)))) (var (S (S (S n))))) 1 (substituteTerm LNN (Succ (var (S (S (S (S n)))))) (S (S (S (S n)))) (var (S (S (S n)))))).
apply (subSubFormula LNN); PRsolveFV A B n.
replace (substituteTerm LNN (Succ (var (S (S (S (S n)))))) (S (S (S (S n)))) (var (S (S (S n))))) with (Succ (substituteTerm LNN (var (S (S (S (S n))))) (S (S (S (S n)))) (var (S (S (S n)))))).
rewrite (subTermVar1 LNN).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
reflexivity.
apply iffSym.
apply (subFormulaTrans LNN); PRsolveFV A B n.
elim H19; symmetry in |- *; assumption.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (var (S (S (S n))))) 1 (var (S (S n)))) (S (S n)) (var (S n))) (S (S (S n))) (var (S (S n)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (var (S (S (S n))))) 1 (var (S n))) (S (S (S n))) (var (S (S n)))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 (var (S (S (S n))))) (S (S (S n))) (var (S (S n)))) 1 (var (S n))).
apply (subFormulaExch LNN); PRsolveFV A B n.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN); PRsolveFV A B n.
apply H3.
intros.
split.
induction H0 as (H0, H2).
induction H1 as (H1, H3).
intros.
assert (forall v : nat, In v (freeVarFormula LNN betaFormula) -> v <= 2).
eapply proj1.
apply betaRepresentable.
assert (forall v : nat, v <> S (S n) -> v <= S (S n) -> v <= S n).
intros.
induction (le_lt_or_eq _ _ H7).
apply lt_n_Sm_le.
assumption.
elim H6; assumption.
unfold primRecSigmaFormula, minimize, existH, andH, forallH, impH, notH in H4; repeat match goal with | H1:(?X1 = ?X2),H2:(?X1 <> ?X2) |- _ => elim H2; apply H1 | H1:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ => elim H2; symmetry in |- *; apply H1 | H:(v = ?X1) |- _ => rewrite H; clear H | H:(?X1 = v) |- _ => rewrite <- H; clear H | H:(In ?X3 (freeVarFormula LNN (fol.existH LNN ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula LNN X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.forallH LNN ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula LNN X2))); [ apply H | clear H ] | H:(In ?X3 (list_remove nat eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X2)); [ eapply In_list_remove1; apply H | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ] | H:(In ?X3 (freeVarFormula LNN (fol.andH LNN ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.impH LNN ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.notH LNN ?X1))) |- _ => assert (In X3 (freeVarFormula LNN X1)); [ apply H | clear H ] | H:(In _ (freeVarFormula LNN (primRecSigmaFormulaHelp _ _ _))) |- _ => decompose sum (freeVarPrimRecSigmaFormulaHelp1 _ _ _ _ H); clear H | H:(In _ (freeVarFormula LNN (primRecPiFormulaHelp _ _ _))) |- _ => decompose sum (freeVarPrimRecPiFormulaHelp1 _ _ _ _ H); clear H | H:(In ?X3 (freeVarFormula LNN A)) |- _ => apply le_trans with n; [ apply H0; apply H | apply le_n_Sn ] | H:(In ?X3 (freeVarFormula LNN B)) |- _ => apply H6; [ clear H | apply H1; apply H ] | H:(In _ (_ ++ _)) |- _ => induction (in_app_or _ _ _ H); clear H | H:(In _ (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ => induction (freeVarSubFormula3 _ _ _ _ _ H); clear H | H:(In _ (freeVarFormula LNN (LT ?X1 ?X2))) |- _ => rewrite freeVarLT in H | H:(In _ (freeVarTerm LNN (natToTerm _))) |- _ => elim (closedNatToTerm _ _ H) | H:(In _ (freeVarTerm LNN Zero)) |- _ => elim H | H:(In _ (freeVarTerm LNN (Succ _))) |- _ => rewrite freeVarSucc in H | H:(In _ (freeVarTerm LNN (var _))) |- _ => simpl in H; decompose sum H; clear H | H:(In _ (freeVarTerm LNN (fol.var LNN _))) |- _ => simpl in H; decompose sum H; clear H end; try first [ assumption | apply le_n ].
assert (v <= 2); auto.
destruct v as [| n0].
apply le_O_n.
destruct n0.
elim H9; reflexivity.
destruct n0.
elim H10; reflexivity.
elim (le_not_lt _ _ H7).
repeat apply lt_n_S.
apply lt_O_Sn.
apply H; auto.
Fixpoint primRecFormula (n : nat) (f : PrimRec n) {struct f} : Formula := match f with | succFunc => succFormula | zeroFunc => zeroFormula | projFunc n m _ => projFormula m | composeFunc n m g h => composeSigmaFormula n n m (primRecsFormula n m g) (primRecFormula m h) | primRecFunc n g h => primRecSigmaFormula n (primRecFormula n g) (primRecFormula (S (S n)) h) end with primRecsFormula (n m : nat) (fs : PrimRecs n m) {struct fs} : Vector.t (Formula * naryFunc n) m := match fs in (PrimRecs n m) return (Vector.t (Formula * naryFunc n) m) with | PRnil n => Vector.nil _ | PRcons n m f fs' => Vector.cons (Formula * naryFunc n) (primRecFormula n f, evalPrimRec n f) m (primRecsFormula n m fs') end.
End Primative_Recursive_Representable.

Remark In_betaFormula_subst_2_1 : forall (a b : Term) (v : nat), In v (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN betaFormula 2 a) 1 b)) -> In v (freeVarTerm LNN a) \/ In v (freeVarTerm LNN b) \/ In v (freeVarTerm LNN (var 0)).
Proof.
intros.
induction (freeVarSubFormula3 _ _ _ _ _ H).
assert (In v (freeVarFormula LNN (substituteFormula LNN betaFormula 2 a))).
eapply In_list_remove1.
apply H0.
decompose sum (In_betaFormula_subst_2 _ _ H1); try tauto.
induction H3 as [H2| H2].
elim (In_list_remove2 _ _ _ _ _ H0).
symmetry in |- *; assumption.
elim H2.
tauto.

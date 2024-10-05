Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import code.
Require Import codeSubFormula.
Require Import folProp.
Require Import folProof.
Require Import Languages.
Require Import subAll.
Require Import subProp.
Require Import folLogic3.
Require Import folReplace.
Require Import LNN.
Require Import codeNatToTerm.
Require Import PRrepresentable.
Require Import ListExt.
Require Import Coq.Lists.List.
Require Import NN.
Require Import expressible.
Definition subStar (a v n : nat) := codeSubFormula a v (codeNatToTerm n).
Section LNN_FixPoint.
Let codeFormula := codeFormula LNN codeLNTFunction codeLNNRelation.
End LNN_FixPoint.
Section LNT_FixPoint.
Require Import PA.
Require Import NN2PA.
Let codeFormula := codeFormula LNT codeLNTFunction codeLNTRelation.
End LNT_FixPoint.

Lemma FixPointLNN : forall (A : Formula) (v : nat), {B : Formula | SysPrf NN (iffH B (substituteFormula LNN A v (natToTermLNN (codeFormula B)))) /\ (forall x : nat, In x (freeVarFormula LNN B) <-> In x (list_remove _ eq_nat_dec v (freeVarFormula LNN A)))}.
Proof.
intros.
set (subStarFormula := primRecFormula _ (proj1_sig subStarIsPR)) in *.
assert (represent : Representable NN 3 subStar subStarFormula).
unfold subStarFormula in |- *.
apply primRecRepresentable.
set (nv := newVar (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)) in *.
assert (0 <> nv).
unfold not in |- *; intros.
elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
unfold nv in H.
rewrite <- H.
simpl in |- *.
right.
auto.
assert (1 <> nv).
unfold not in |- *; intros.
elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
unfold nv in H0.
rewrite <- H0.
simpl in |- *.
auto.
assert (2 <> nv).
unfold not in |- *; intros.
elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
unfold nv in H1.
rewrite <- H1.
simpl in |- *.
auto.
assert (3 <> nv).
unfold not in |- *; intros.
elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
unfold nv in H2.
rewrite <- H2.
simpl in |- *.
auto.
assert (3 < nv).
destruct nv as [| n].
elim H; auto.
destruct n.
elim H0; auto.
destruct n.
elim H1; auto.
destruct n.
elim H2; auto.
repeat apply lt_n_S.
apply lt_O_Sn.
set (Theta := existH v (andH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN subStarFormula 3 (var nv)) 2 (natToTerm nv)) 1 (var nv)) 0 (var v)) A)) in *.
exists (substituteFormula LNN Theta nv (natToTerm (codeFormula Theta))).
split.
set (N := natToTermLNN (codeFormula (substituteFormula LNN Theta nv (natToTerm (codeFormula Theta))))) in *.
unfold Theta at 1 in |- *.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec v nv).
elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
fold nv in |- *.
simpl in |- *.
auto.
induction (In_dec eq_nat_dec v (freeVarTerm LNN (natToTerm (codeFormula Theta)))).
elim (closedNatToTerm _ _ a).
clear b b0.
rewrite (subFormulaAnd LNN).
apply iffTrans with (existH v (andH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN subStarFormula 3 (natToTerm (codeFormula Theta))) 2 (natToTerm nv)) 1 (natToTerm (codeFormula Theta))) 0 (var v)) A)).
apply (reduceExist LNN).
apply closedNN.
apply (reduceAnd LNN).
eapply iffTrans.
apply (subFormulaExch LNN).
assumption.
unfold not in |- *; intros.
induction H4 as [H4| H4].
elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
fold nv in |- *.
rewrite <- H4.
simpl in |- *.
auto.
apply H4.
apply closedNatToTerm.
apply (reduceSub LNN).
apply closedNN.
eapply iffTrans.
apply (subSubFormula LNN).
assumption.
apply closedNatToTerm.
rewrite (subTermVar1 LNN).
apply (reduceSub LNN).
apply closedNN.
eapply iffTrans.
apply (subFormulaExch LNN).
assumption.
apply closedNatToTerm.
apply closedNatToTerm.
apply (reduceSub LNN).
apply closedNN.
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In nv (freeVarFormula LNN subStarFormula)).
eapply In_list_remove1.
apply H4.
induction represent as (H6, H7).
elim (lt_not_le _ _ H3).
auto.
apply (subFormulaNil LNN).
unfold not in |- *; intros.
elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
fold nv in |- *.
simpl in |- *.
repeat right.
auto.
apply iffI.
apply impI.
apply existSys.
apply closedNN.
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H4).
elim (In_list_remove2 _ _ _ _ _ H5).
auto.
elim (closedNatToTerm _ _ H5).
apply impE with (substituteFormula LNN (equal (var 0) N) 0 (var v)).
rewrite (subFormulaEqual LNN).
rewrite (subTermVar1 LNN).
rewrite (subTermNil LNN).
apply impI.
apply impE with (substituteFormula LNN A v (var v)).
apply (subWithEquals LNN).
apply Axm; right; constructor.
rewrite (subFormulaId LNN).
eapply andE2.
apply Axm; left; right; constructor.
unfold N in |- *.
apply closedNatToTerm.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN subStarFormula 3 (natToTerm (codeFormula Theta))) 2 (natToTerm nv)) 1 (natToTerm (codeFormula Theta))) 0 (var v)).
apply iffE1.
apply sysWeaken.
apply (reduceSub LNN).
apply closedNN.
induction represent as (H4, H5).
simpl in H5.
unfold N in |- *.
replace (codeFormula (substituteFormula LNN Theta nv (natToTerm (codeFormula Theta)))) with (subStar (codeFormula Theta) nv (codeFormula Theta)).
apply H5.
unfold subStar in |- *.
rewrite codeNatToTermCorrectLNN.
unfold codeFormula at 1 in |- *.
rewrite codeSubFormulaCorrect.
reflexivity.
eapply andE1.
apply Axm; right; constructor.
apply impI.
apply existI with N.
rewrite (subFormulaAnd LNN).
apply andI.
apply sysWeaken.
eapply impE with (substituteFormula LNN (substituteFormula LNN (equal (var 0) N) 0 (var v)) v N).
apply iffE2.
apply (reduceSub LNN).
apply closedNN.
apply (reduceSub LNN).
apply closedNN.
induction represent as (H4, H5).
simpl in H5.
unfold N in |- *.
replace (codeFormula (substituteFormula LNN Theta nv (natToTerm (codeFormula Theta)))) with (subStar (codeFormula Theta) nv (codeFormula Theta)).
apply H5.
unfold subStar in |- *.
rewrite codeNatToTermCorrectLNN.
unfold codeFormula at 1 in |- *.
rewrite codeSubFormulaCorrect.
reflexivity.
repeat rewrite (subFormulaEqual LNN).
repeat rewrite (subTermVar1 LNN).
repeat rewrite (subTermNil LNN N).
apply eqRefl.
unfold N in |- *.
apply closedNatToTerm.
unfold N in |- *.
apply closedNatToTerm.
apply Axm; right; constructor.
intro.
split.
intro.
unfold Theta at 1 in H4.
unfold existH, andH in H4.
induction represent as (H5, H6).
repeat match goal with | H1:(?X1 = ?X2),H2:(?X1 <> ?X2) |- _ => elim H2; apply H1 | H1:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ => elim H2; symmetry in |- *; apply H1 | H:(In ?X3 (freeVarFormula LNN (fol.existH LNN ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula LNN X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.forallH LNN ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula LNN X2))); [ apply H | clear H ] | H:(In ?X3 (list_remove nat eq_nat_dec ?X1 (freeVarFormula LNN ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X2)); [ eapply In_list_remove1; apply H | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ] | H:(In ?X3 (freeVarFormula LNN (fol.andH LNN ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.impH LNN ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula LNN X1 ++ freeVarFormula LNN X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula LNN (fol.notH LNN ?X1))) |- _ => assert (In X3 (freeVarFormula LNN X1)); [ apply H | clear H ] | H:(In _ (_ ++ _)) |- _ => induction (in_app_or _ _ _ H); clear H | H:(In _ (freeVarFormula LNN (substituteFormula LNN ?X1 ?X2 ?X3))) |- _ => induction (freeVarSubFormula3 _ _ _ _ _ H); clear H | H:(In _ (freeVarTerm LNN (natToTerm _))) |- _ => elim (closedNatToTerm _ _ H) | H:(In _ (freeVarTerm LNN Zero)) |- _ => elim H | H:(In _ (freeVarTerm LNN (Succ _))) |- _ => rewrite freeVarSucc in H | H:(In _ (freeVarTerm LNN (var _))) |- _ => simpl in H; decompose sum H; clear H | H:(In _ (freeVarTerm LNN (fol.var LNN _))) |- _ => simpl in H; decompose sum H; clear H end.
elim (le_not_lt _ _ (H5 _ H4)).
destruct x as [| n].
elim H10; auto.
destruct n.
elim H11; auto.
destruct n.
elim H12; auto.
destruct n.
elim H13; auto.
repeat apply lt_n_S.
apply lt_O_Sn.
apply In_list_remove3; auto.
intro.
assert (In x (freeVarFormula LNN A)); [ eapply In_list_remove1; apply H4 | assert (x <> v); [ eapply In_list_remove2; apply H4 | clear H4 ] ].
apply freeVarSubFormula1.
unfold not in |- *; intros.
rewrite <- H4 in H5.
elim (newVar1 (v :: 1 :: 2 :: 3 :: 0 :: freeVarFormula LNN A)).
fold nv in |- *.
simpl in |- *.
repeat right.
auto.
unfold Theta in |- *.
apply (In_list_remove3 nat eq_nat_dec x v (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN subStarFormula 3 (var nv)) 2 (natToTerm nv)) 1 (var nv)) 0 (var v)) ++ freeVarFormula LNN A)).
apply in_or_app.
auto.
assumption.

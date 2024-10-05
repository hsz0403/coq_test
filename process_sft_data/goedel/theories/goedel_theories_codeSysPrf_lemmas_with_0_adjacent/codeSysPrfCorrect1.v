Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import checkPrf.
Require Import code.
Require Import Languages.
Require Import folProp.
Require Import folProof.
Require Import folLogic3.
Require Import folReplace.
Require Import PRrepresentable.
Require Import expressible.
Require Import primRec.
Require Import Arith.
Require Import PA.
Require Import NNtheory.
Require Import codeList.
Require Import subProp.
Require Import ListExt.
Require Import cPair.
Require Import wellFormed.
Require Import prLogic.
Ltac SimplFreeVar := repeat match goal with | H1:(?X1 = ?X2),H2:(?X1 <> ?X2) |- _ => elim H2; apply H1 | H1:(?X1 = ?X2),H2:(?X2 <> ?X1) |- _ => elim H2; symmetry in |- *; apply H1 | H1:(?X1 <> ?X1) |- _ => elim H1; reflexivity | H:(In ?X3 (freeVarFormula ?X9 (existH ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula X9 X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.existH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula X9 X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (forallH ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula X9 X2))); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.forallH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (list_remove nat eq_nat_dec X1 (freeVarFormula X9 X2))); [ apply H | clear H ] | H:(In ?X3 (list_remove nat eq_nat_dec ?X1 (freeVarFormula ?X9 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X2)); [ eapply In_list_remove1; apply H | assert (X3 <> X1); [ eapply In_list_remove2; apply H | clear H ] ] | H:(In ?X3 (freeVarFormula ?X9 (andH ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.andH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (orH ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.orH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (impH ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.impH ?X9 ?X1 ?X2))) |- _ => assert (In X3 (freeVarFormula X9 X1 ++ freeVarFormula X9 X2)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (notH ?X1))) |- _ => assert (In X3 (freeVarFormula X9 X1)); [ apply H | clear H ] | H:(In ?X3 (freeVarFormula ?X9 (fol.notH ?X9 ?X1))) |- _ => assert (In X3 (freeVarFormula X9 X1)); [ apply H | clear H ] | H:(In _ (_ ++ _)) |- _ => induction (in_app_or _ _ _ H); clear H | H:(In _ (freeVarFormula ?X9 (substituteFormula ?X9 ?X1 ?X2 ?X3))) |- _ => induction (freeVarSubFormula3 _ _ _ _ _ H); clear H | H:(In _ (freeVarFormula ?X9 (LT ?X1 ?X2))) |- _ => rewrite freeVarLT in H | H:(In _ (freeVarTerm ?X9 (LNT.natToTerm _))) |- _ => elim (LNT.closedNatToTerm _ _ H) | H:(In _ (freeVarTerm ?X9 (natToTerm _))) |- _ => elim (closedNatToTerm _ _ H) | H:(In _ (freeVarTerm ?X9 Zero)) |- _ => elim H | H:(In _ (freeVarTerm ?X9 (Succ _))) |- _ => rewrite freeVarSucc in H | H:(In _ (freeVarTerm ?X9 (var _))) |- _ => simpl in H; decompose sum H; clear H | H:(In _ (freeVarTerm ?X9 (LNT.var _))) |- _ => simpl in H; decompose sum H; clear H | H:(In _ (freeVarTerm ?X9 (fol.var ?X9 _))) |- _ => simpl in H; decompose sum H; clear H end.
Section code_SysPrf.
Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Variable codeArityF : nat -> nat.
Variable codeArityR : nat -> nat.
Hypothesis codeArityFIsPR : isPR 1 codeArityF.
Hypothesis codeArityFIsCorrect1 : forall f : Functions L, codeArityF (codeF f) = S (arity L (inr _ f)).
Hypothesis codeArityFIsCorrect2 : forall n : nat, codeArityF n <> 0 -> exists f : Functions L, codeF f = n.
Hypothesis codeArityRIsPR : isPR 1 codeArityR.
Hypothesis codeArityRIsCorrect1 : forall r : Relations L, codeArityR (codeR r) = S (arity L (inl _ r)).
Hypothesis codeArityRIsCorrect2 : forall n : nat, codeArityR n <> 0 -> exists r : Relations L, codeR r = n.
Hypothesis codeFInj : forall f g : Functions L, codeF f = codeF g -> f = g.
Hypothesis codeRInj : forall R S : Relations L, codeR R = codeR S -> R = S.
Section LNN.
Variable T : System.
Hypothesis TextendsNN : Included _ NN T.
Variable U : fol.System L.
Variable fU : Formula.
Variable v0 : nat.
Hypothesis freeVarfU : forall v : nat, In v (freeVarFormula LNN fU) -> v = v0.
Hypothesis expressU1 : forall f : fol.Formula L, mem _ U f -> SysPrf T (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR f))).
Hypothesis expressU2 : forall f : fol.Formula L, ~ mem _ U f -> SysPrf T (notH (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR f)))).
Definition codeSysPrf : Formula := let nv := newVar (2 :: 1 :: 0 :: v0 :: nil) in existH nv (andH (substituteFormula LNN (substituteFormula LNN (primRecFormula 2 (proj1_sig (checkPrfIsPR L codeF codeR codeArityF codeArityR codeArityFIsPR codeArityRIsPR))) 0 (Succ (var nv))) 2 (var 0)) (forallH (S nv) (impH (LT (var (S nv)) (var nv)) (orH (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (primRecFormula 2 (proj1_sig codeInIsPR)) 2 (var (S nv))) 1 (var nv)) 0 Zero) (substituteFormula LNN fU v0 (var (S nv))))))).
Definition codeSysPf : Formula := existH 1 codeSysPrf.
Definition codeSysPrfNot := existH 2 (andH (substituteFormula LNN codeSysPrf 0 (var 2)) (substituteFormula LNN (substituteFormula LNN (primRecFormula 1 (proj1_sig codeNotIsPR)) 0 (var 2)) 1 (var 0))).
End LNN.
End code_SysPrf.

Lemma codeSysPrfCorrect1 : forall (f : fol.Formula L) (A : list (fol.Formula L)) (p : Prf L A f), (forall g : fol.Formula L, In g A -> mem _ U g) -> SysPrf T (substituteFormula LNN (substituteFormula LNN codeSysPrf 0 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A f p))).
Proof.
intros.
unfold codeSysPrf in |- *.
set (nvl := 2 :: 1 :: 0 :: v0 :: nil) in *.
set (nv := newVar nvl) in *.
assert (nv <> 0).
unfold nv, not in |- *; intros; elim (newVar1 nvl).
rewrite H0; unfold nvl in |- *.
simpl in |- *; auto.
assert (nv <> 1).
unfold nv, not in |- *; intros; elim (newVar1 nvl).
rewrite H1; unfold nvl in |- *.
simpl in |- *; auto.
assert (nv <> 2).
unfold nv, not in |- *; intros; elim (newVar1 nvl).
rewrite H2; unfold nvl in |- *.
simpl in |- *; auto.
assert (nv <> v0).
unfold nv, not in |- *; intros; elim (newVar1 nvl).
rewrite H3; unfold nvl in |- *.
simpl in |- *; auto.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec nv 0).
elim H0; assumption.
induction (In_dec eq_nat_dec nv (freeVarTerm LNN (natToTerm (codeFormula L codeF codeR f)))).
elim (closedNatToTerm _ _ a).
clear b b0.
rewrite (subFormulaExist LNN).
induction (eq_nat_dec nv 1).
elim H1; assumption.
induction (In_dec eq_nat_dec nv (freeVarTerm LNN (natToTerm (codePrf L codeF codeR A f p)))).
elim (closedNatToTerm _ _ a).
clear b b0.
apply existI with (natToTerm (codeList (map (codeFormula L codeF codeR) A))).
repeat rewrite (subFormulaAnd LNN).
apply andI.
apply sysExtend with NN.
apply TextendsNN.
set (B := primRecFormula 2 (proj1_sig (checkPrfIsPR L codeF codeR codeArityF codeArityR codeArityFIsPR codeArityRIsPR))) in *.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 0 (Succ (var nv))) 2 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A f p))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In 0 (freeVarFormula LNN (substituteFormula LNN B 0 (Succ (var nv))))).
eapply In_list_remove1.
apply H4.
induction (freeVarSubFormula3 _ _ _ _ _ H5).
elim (In_list_remove2 _ _ _ _ _ H6).
reflexivity.
simpl in H6.
decompose sum H6.
auto.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A f p))) 0 (Succ (var nv))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN B 2 (natToTerm (codeFormula L codeF codeR f))) 0 (Succ (var nv))) 1 (natToTerm (codePrf L codeF codeR A f p))).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
discriminate.
simpl in |- *.
unfold not in |- *; intros.
decompose sum H4.
apply H2; assumption.
apply closedNatToTerm.
apply (subFormulaExch LNN).
discriminate.
simpl in |- *.
unfold not in |- *; intros.
decompose sum H4.
apply H1; assumption.
apply closedNatToTerm.
unfold B in |- *.
clear B.
assert (Representable NN 2 (checkPrf L codeF codeR codeArityF codeArityR) (primRecFormula 2 (proj1_sig (checkPrfIsPR L codeF codeR codeArityF codeArityR codeArityFIsPR codeArityRIsPR)))).
apply primRecRepresentable.
induction H4 as (H4, H5).
set (F := primRecFormula 2 (proj1_sig (checkPrfIsPR L codeF codeR codeArityF codeArityR codeArityFIsPR codeArityRIsPR))) in *.
simpl in H5.
apply impE with (substituteFormula LNN (substituteFormula LNN (equal (var 0) (natToTerm (checkPrf L codeF codeR codeArityF codeArityR (codeFormula L codeF codeR f) (codePrf L codeF codeR A f p)))) 0 (Succ (var nv))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H5.
rewrite (subFormulaEqual LNN).
rewrite (subTermVar1 LNN).
rewrite (subTermNil LNN).
rewrite (subFormulaEqual LNN).
replace (substituteTerm LNN (Succ (var nv)) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) with (natToTerm (S (codeList (map (codeFormula L codeF codeR) A)))).
rewrite (subTermNil LNN).
rewrite checkPrfCorrect1.
apply eqRefl.
apply codeArityFIsCorrect1.
apply codeArityRIsCorrect1.
apply closedNatToTerm.
generalize nv.
intro.
simpl in |- *.
induction (eq_nat_dec nv0 nv0).
reflexivity.
elim b.
reflexivity.
apply closedNatToTerm.
assert (S nv <> 1).
unfold not in |- *; intros.
elim (le_not_lt (S nv) 1).
rewrite H4.
apply le_n.
apply lt_S.
unfold nv in |- *.
apply newVar2.
unfold nvl in |- *; simpl in |- *; auto.
assert (S nv <> 2).
unfold not in |- *; intros.
elim (le_not_lt (S nv) 2).
rewrite H5.
apply le_n.
apply lt_S.
unfold nv in |- *.
apply newVar2.
unfold nvl in |- *; simpl in |- *; auto.
assert (S nv <> nv).
unfold not in |- *; intros.
eapply (n_Sn nv).
symmetry in |- *; assumption.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec (S nv) 0).
discriminate a.
induction (In_dec eq_nat_dec (S nv) (freeVarTerm LNN (natToTerm (codeFormula L codeF codeR f)))).
elim (closedNatToTerm _ _ a).
clear b b0.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec (S nv) 1).
elim H4; assumption.
induction (In_dec eq_nat_dec (S nv) (freeVarTerm LNN (natToTerm (codePrf L codeF codeR A f p)))).
elim (closedNatToTerm _ _ a).
clear b b0.
rewrite (subFormulaForall LNN).
induction (eq_nat_dec (S nv) nv).
elim H6; assumption.
induction (In_dec eq_nat_dec (S nv) (freeVarTerm LNN (natToTerm (codeList (map (codeFormula L codeF codeR) A))))).
elim (closedNatToTerm _ _ a).
clear b b0.
repeat rewrite (subFormulaImp LNN).
replace (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (LT (var (S nv)) (var nv)) 0 (natToTerm (codeFormula L codeF codeR f))) 1 (natToTerm (codePrf L codeF codeR A f p))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) with (LT (var (S nv)) (natToTerm (codeList (map (codeFormula L codeF codeR) A)))).
set (G := list_rec (fun _ => Formula) (equal Zero Zero) (fun (a : fol.Formula L) _ (rec : Formula) => andH (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR a))) rec) A) in *.
assert (forall v : nat, ~ In v (freeVarFormula LNN G)).
unfold G in |- *.
intros.
generalize A.
intro.
induction A0 as [| a A0 HrecA0].
simpl in |- *.
auto.
simpl in |- *.
unfold not in |- *; intros.
induction (in_app_or _ _ _ H7).
induction (freeVarSubFormula3 _ _ _ _ _ H8).
absurd (v = v0).
eapply In_list_remove2.
apply H9.
apply freeVarfU.
eapply In_list_remove1.
apply H9.
elim (closedNatToTerm _ _ H9).
auto.
apply impE with G.
apply sysExtend with NN.
assumption.
apply impI.
assert (forall v : nat, ~ In_freeVarSys LNN v (Ensembles.Add (fol.Formula LNN) NN G)).
unfold not in |- *; intros.
induction H8 as (x, H8).
induction H8 as (H8, H9).
induction H9 as [x H9| x H9].
elim (closedNN v).
exists x.
auto.
induction H9.
apply (H7 v).
assumption.
apply forallI.
apply H8.
apply impI.
apply impE with G.
apply impE with (LT (var (S nv)) (natToTerm (codeList (map (codeFormula L codeF codeR) A)))).
repeat simple apply sysWeaken.
apply boundedLT.
intros.
rewrite (subFormulaImp LNN).
apply impTrans with G.
apply iffE1.
apply (subFormulaNil LNN).
apply H7.
apply impI.
repeat rewrite (subFormulaOr LNN).
induction (In_dec eq_nat_dec n (map (codeFormula L codeF codeR) A)).
apply orI2.
apply impE with (substituteFormula LNN fU v0 (natToTerm n)).
apply iffE2.
apply sysWeaken.
assert (forall v : nat, ~ In v (list_remove nat eq_nat_dec v0 (freeVarFormula LNN fU))).
unfold not in |- *; intros.
absurd (v = v0).
eapply In_list_remove2.
apply H10.
apply freeVarfU.
eapply In_list_remove1.
apply H10.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN fU v0 (var (S nv))) 1 (natToTerm (codePrf L codeF codeR A f p))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H11).
apply (H10 0).
assumption.
simpl in H12.
decompose sum H12.
discriminate H13.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN fU v0 (var (S nv))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H11).
apply (H10 1).
assumption.
simpl in H12.
decompose sum H12.
apply H4; assumption.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN fU v0 (var (S nv))) (S nv) (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H11).
apply (H10 nv).
assumption.
simpl in H12.
decompose sum H12.
apply H6; assumption.
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
absurd (S nv = v0).
unfold not in |- *; intros.
elim (le_not_lt (S nv) v0).
rewrite H12.
apply le_n.
apply lt_S.
unfold nv in |- *.
apply newVar2.
unfold nvl in |- *; simpl in |- *; auto.
apply freeVarfU.
eapply In_list_remove1.
apply H11.
clear H9 H8 H7 H p.
induction A as [| a0 A HrecA].
elim a.
simpl in (value of G).
simpl in a.
induction a as [H| H].
unfold G in |- *.
rewrite H.
eapply andE1.
apply Axm; right; constructor.
apply impE with (list_rec (fun _ => Formula) (equal Zero Zero) (fun (a : fol.Formula L) (_ : list (fol.Formula L)) (rec : Formula) => andH (substituteFormula LNN fU v0 (natToTerm (codeFormula L codeF codeR a))) rec) A).
apply sysWeaken.
apply impI.
apply HrecA.
assumption.
eapply andE2.
unfold G in |- *.
apply Axm; right; constructor.
apply orI1.
assert (Representable NN 2 codeIn (primRecFormula 2 (proj1_sig codeInIsPR))).
apply primRecRepresentable.
induction H10 as (H10, H11).
set (J := primRecFormula 2 (proj1_sig codeInIsPR)) in *.
simpl in H11.
apply sysWeaken.
apply impE with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (natToTerm n)) 1 (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) 0 Zero).
apply iffE2.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) 0 Zero) 1 (natToTerm (codePrf L codeF codeR A f p))) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H12).
elim (In_list_remove2 _ _ _ _ _ H13).
reflexivity.
apply H13.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) 0 Zero) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaNil LNN).
unfold not in |- *; intros.
induction (freeVarSubFormula3 _ _ _ _ _ H12).
assert (In 1 (freeVarFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)))).
eapply In_list_remove1.
apply H13.
induction (freeVarSubFormula3 _ _ _ _ _ H14).
elim (In_list_remove2 _ _ _ _ _ H15).
reflexivity.
simpl in H15.
decompose sum H15.
apply H1; assumption.
apply H13.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (var nv)) nv (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) 0 Zero) (S nv) (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
unfold not in |- *; intros; apply H0; symmetry in |- *; assumption.
auto.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) 0 Zero) (S nv) (natToTerm n)).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
assert (In nv (freeVarFormula LNN (substituteFormula LNN J 2 (var (S nv))))).
eapply In_list_remove1.
apply H12.
induction (freeVarSubFormula3 _ _ _ _ _ H13).
apply (le_not_lt nv 2).
apply H10.
eapply In_list_remove1.
apply H14.
destruct nv as [| n0].
elim H0; reflexivity.
destruct n0.
elim H1; reflexivity.
destruct n0.
elim H2; reflexivity.
repeat apply lt_n_S.
apply lt_O_Sn.
simpl in H14.
decompose sum H14.
apply H6; assumption.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) 1 (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) (S nv) (natToTerm n)) 0 Zero).
apply (subFormulaExch LNN).
discriminate.
auto.
apply closedNatToTerm.
apply iffTrans with (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN (substituteFormula LNN J 2 (var (S nv))) (S nv) (natToTerm n)) 1 (natToTerm (codeList (map (codeFormula L codeF codeR) A)))) 0 Zero).
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaExch LNN).
unfold not in |- *; intros; apply H4; symmetry in |- *; assumption.
apply closedNatToTerm.
apply closedNatToTerm.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply (subFormulaTrans LNN).
unfold not in |- *; intros.
apply (le_not_lt (S nv) 2).
apply H10.
eapply In_list_remove1.
apply H12.
apply le_lt_n_Sm.
destruct nv as [| n0].
elim H0; reflexivity.
destruct n0.
elim H1; reflexivity.
repeat apply le_n_S.
apply le_O_n.
apply impE with (substituteFormula LNN (equal (var 0) (natToTerm (codeIn n (codeList (map (codeFormula L codeF codeR) A))))) 0 Zero).
apply iffE2.
repeat (apply (reduceSub LNN); [ apply closedNN | idtac ]).
apply H11.
rewrite codeInCorrect.
induction (In_dec eq_nat_dec n (map (codeFormula L codeF codeR) A)).
elim b; assumption.
rewrite (subFormulaEqual LNN).
rewrite (subTermVar1 LNN).
rewrite (subTermNil LNN).
apply eqRefl.
apply closedNatToTerm.
apply Axm; right; constructor.
apply Axm; left; right; constructor.
clear p H7.
induction A as [| a A HrecA]; simpl in (value of G).
unfold G in |- *.
apply eqRefl.
simpl in H.
unfold G in |- *.
apply andI.
apply expressU1.
apply H.
auto.
apply HrecA.
intros.
apply H.
auto.
assert (forall (t1 t2 s : Term) (v : nat), substituteFormula LNN (LT t1 t2) v s = LT (substituteTerm LNN t1 v s) (substituteTerm LNN t2 v s)).
reflexivity.
repeat rewrite H7.
repeat rewrite (subTermVar1 LNN) || rewrite (subTermVar2 LNN); try unfold not in |- *; intros.
reflexivity.
apply H1; auto.
apply H0; auto.
apply H6; auto.
apply H4; auto.
discriminate H8.

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

Lemma freeVarCodeSysPf : forall v : nat, In v (freeVarFormula LNN codeSysPf) -> v = 0.
Proof.
intros.
unfold codeSysPf in H.
destruct v as [| n].
reflexivity.
destruct n.
elim (In_list_remove2 _ _ _ _ _ H).
reflexivity.
elim (le_not_lt (S (S n)) 1).
apply freeVarCodeSysPrf.
eapply In_list_remove1.
apply H.
apply lt_n_S.
apply lt_O_Sn.

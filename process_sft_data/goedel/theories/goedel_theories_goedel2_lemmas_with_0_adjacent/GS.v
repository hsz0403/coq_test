Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import folProp.
Require Import folProof.
Require Import folReplace.
Require Import folLogic3.
Require Import subProp.
Require Import ListExt.
Require Import fixPoint.
Require Import NN2PA.
Require Import codeSysPrf.
Require Import PAtheory.
Require Import code.
Require Import checkPrf.
Require Import codeNatToTerm.
Require Import rosserPA.
Section Goedel's_2nd_Incompleteness.
Variable T : System.
Hypothesis extendsPA : Included _ PA T.
Variable repT : Formula.
Variable v0 : nat.
Hypothesis freeVarRepT : forall v : nat, In v (freeVarFormula LNT repT) -> v = v0.
Hypothesis expressT1 : forall f : Formula, mem _ T f -> SysPrf T (substituteFormula LNT repT v0 (natToTerm (codeFormula f))).
Hypothesis expressT2 : forall f : Formula, ~ mem _ T f -> SysPrf T (notH (substituteFormula LNT repT v0 (natToTerm (codeFormula f)))).
Definition codeSysPf := (codeSysPf LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTRIsPR (LNT2LNN_formula repT) v0).
Section Goedel1PA.
Definition T' := T' T.
Definition extendsNN := extendsNN T.
Definition Tprf2T'prf := Tprf2T'prf T.
Definition expressT'1 := expressT'1 T repT v0 expressT1.
Definition expressT'2 := expressT'2 T repT v0 expressT2.
Definition freeVarRepT' := freeVarRepT' repT v0 freeVarRepT.
Definition codeSysPfCorrect := codeSysPfCorrect LNT codeLNTFunction codeLNTRelation codeArityLNTF codeArityLNTR codeArityLNTFIsPR codeArityLNTFIsCorrect1 codeArityLNTRIsPR codeArityLNTRIsCorrect1 T' extendsNN T (LNT2LNN_formula repT) v0 freeVarRepT' expressT'1.
Definition G := let (a,_) := FixPointLNT (notH (LNN2LNT_formula codeSysPf)) 0 in a.
Definition box (f:Formula) := (substituteFormula LNT (LNN2LNT_formula codeSysPf) 0 (natToTerm (codeFormula f))).
End Goedel1PA.
Definition F := (notH (forallH 0 (equal (var 0) (var 0)))).
Definition Con := notH (box F).
Hypothesis HBL2 : forall f, SysPrf T (impH (box f) (box (box f))).
Hypothesis HBL3 : forall f g, SysPrf T (impH (box (impH f g)) (impH (box f) (box g))).
End Goedel's_2nd_Incompleteness.

Lemma GS : SysPrf T (iffH G (notH (box G))).
Proof.
unfold G.
destruct (FixPointLNT (notH (LNN2LNT_formula codeSysPf)) 0).
destruct a.
unfold box.
apply sysExtend with PA.
assumption.
rewrite <- (subFormulaNot LNT).
apply H.

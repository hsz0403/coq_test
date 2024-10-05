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

Lemma subStarIsPR : isPR 3 subStar.
Proof.
unfold subStar in |- *.
apply compose3_3IsPR with (f1 := fun a v n : nat => a) (f2 := fun a v n : nat => v) (f3 := fun a v n : nat => codeNatToTerm n).
apply pi1_3IsPR.
apply pi2_3IsPR.
apply filter001IsPR.
apply codeNatToTermIsPR.
apply codeSubFormulaIsPR.

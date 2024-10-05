Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProp.
Require Import folProof.
Require Export folLogic.
Require Import subProp.
Require Import folReplace.
Require Import Arith.
Section More_Logic_Rules.
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
End More_Logic_Rules.

Lemma subSubTerms : forall (n : nat) (ts : Terms n) (v1 v2 : nat) (s1 s2 : Term), v1 <> v2 -> ~ In v1 (freeVarTerm L s2) -> substituteTerms L n (substituteTerms L n ts v1 s1) v2 s2 = substituteTerms L n (substituteTerms L n ts v2 s2) v1 (substituteTerm L s1 v2 s2).
Proof.
intros.
induction ts as [| n t ts Hrects].
reflexivity.
simpl in |- *.
rewrite Hrects.
rewrite subSubTerm.
reflexivity.
auto.
auto.

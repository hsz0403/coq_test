Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import extEqualNat.
Require Vector.
Section Code_Substitute_Term.
Variable L : Language.
Variable codeF : Functions L -> nat.
Let Formula := Formula L.
Let Formulas := Formulas L.
Let System := System L.
Let Term := Term L.
Let Terms := Terms L.
Let var := var L.
Let apply := apply L.
Definition codeSubTermTerms : nat -> nat -> nat -> nat := evalStrongRec 2 (fun t recs v s : nat => cPair (switchPR (cPairPi1 t) (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) (switchPR (charFunction 2 beq_nat (cPairPi2 t) v) s t)) (switchPR t (S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0)).
Definition codeSubTerm (t s v : nat) : nat := cPairPi1 (codeSubTermTerms t s v).
Definition codeSubTerms (t s v : nat) : nat := cPairPi2 (codeSubTermTerms t s v).
End Code_Substitute_Term.

Lemma codeSubTermsCorrect : forall (n : nat) (ts : Terms n) (v : nat) (s : Term), codeSubTerms (codeTerms L codeF n ts) v (codeTerm L codeF s) = codeTerms L codeF n (substituteTerms L n ts v s).
Proof.
set (g := fun t0 recs v0 s0 : nat => cPair (switchPR (cPairPi1 t0) (cPair (cPairPi1 t0) (cPairPi2 (codeNth (t0 - S (cPairPi2 t0)) recs))) (switchPR (charFunction 2 beq_nat (cPairPi2 t0) v0) s0 t0)) (switchPR t0 (S (cPair (cPairPi1 (codeNth (t0 - S (cPairPi1 (pred t0))) recs)) (cPairPi2 (codeNth (t0 - S (cPairPi2 (pred t0))) recs)))) 0)) in *.
intros.
induction ts as [| n t ts Hrects].
simpl in |- *.
unfold codeTerms in |- *.
unfold codeSubTerms in |- *.
unfold codeSubTermTerms in |- *.
unfold evalStrongRec in |- *.
simpl in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
reflexivity.
simpl in |- *.
transitivity (S (cPair (codeTerm L codeF (substituteTerm L t v s)) (codeTerms L codeF n (substituteTerms L n ts v s)))).
rewrite <- Hrects.
rewrite <- codeSubTermCorrect.
replace (codeTerms L codeF (S n) (Tcons L n t ts)) with (S (cPair (codeTerm L codeF t) (codeTerms L codeF n ts))).
generalize (codeTerm L codeF t) (codeTerms L codeF n ts).
clear Hrects ts t n.
intros.
unfold codeSubTerms at 1 in |- *.
unfold codeSubTermTerms in |- *.
fold g in |- *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold g at 1 in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
unfold pred in |- *.
repeat rewrite cPairProjections1 || rewrite cPairProjections2.
assert (extEqual _ (evalComposeFunc 2 1 (Vector.cons _ (evalStrongRecHelp 2 g (S (cPair n n0))) 0 (Vector.nil _)) (fun b : nat => codeNth (S (cPair n n0) - S n) b)) (evalStrongRec 2 g n)).
apply (evalStrongRecHelp2 2).
apply le_lt_n_Sm.
apply cPairLe1.
simpl in H.
rewrite H.
clear H.
assert (extEqual _ (evalComposeFunc 2 1 (Vector.cons _ (evalStrongRecHelp 2 g (S (cPair n n0))) 0 (Vector.nil _)) (fun b : nat => codeNth (S (cPair n n0) - S n0) b)) (evalStrongRec 2 g n0)).
apply (evalStrongRecHelp2 2).
apply le_lt_n_Sm.
apply cPairLe2.
simpl in H.
rewrite H.
clear H.
simpl in |- *.
reflexivity.
reflexivity.
reflexivity.

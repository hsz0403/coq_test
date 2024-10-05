Require Import primRec.
Require Import cPair.
Require Import Arith.
Require Import folProp.
Require Import code.
Require Import extEqualNat.
Require Vector.
Require Import codeSubTerm.
Require Import codeFreeVar.
Require Import Max.
Section Code_Substitute_Formula.
Variable L : Language.
Variable codeF : Functions L -> nat.
Variable codeR : Relations L -> nat.
Notation Formula := (Formula L) (only parsing).
Notation Formulas := (Formulas L) (only parsing).
Notation System := (System L) (only parsing).
Notation Term := (Term L) (only parsing).
Notation Terms := (Terms L) (only parsing).
Let var := var L.
Let apply := apply L.
Let codeFormula := codeFormula L codeF codeR.
Let codeTerm := codeTerm L codeF.
Definition cTriple (a b c : nat) : nat := cPair a (cPair b c).
Definition cTriplePi1 (n : nat) : nat := cPairPi1 n.
Definition cTriplePi2 (n : nat) : nat := cPairPi1 (cPairPi2 n).
Definition cTriplePi3 (n : nat) : nat := cPairPi2 (cPairPi2 n).
Definition codeNewVar (l : nat) : nat := evalStrongRec 0 (fun n Hrecs : nat => switchPR n (max (S (cPairPi1 (pred n))) (codeNth (n - S (cPairPi2 (pred n))) Hrecs)) 0) l.
Definition checkSubFormulaTrace : nat -> nat := evalStrongRec 0 (fun trace recs : nat => let v := cTriplePi1 (cTriplePi1 trace) in let s := cTriplePi2 (cTriplePi1 trace) in let input := cTriplePi3 (cTriplePi1 trace) in let output := cTriplePi2 trace in let rest := cTriplePi3 trace in let type := cPairPi1 input in switchPR type (switchPR (pred type) (switchPR (pred (pred type)) (switchPR (pred (pred (pred type))) (charFunction 2 beq_nat output (cPair type (codeSubTerms (cPairPi2 input) v s))) (switchPR (charFunction 2 beq_nat v (cPairPi1 (cPairPi2 input))) (charFunction 2 beq_nat input output) (switchPR (codeIn (cPairPi1 (cPairPi2 input)) (codeFreeVarTerm s)) (let nv := codeNewVar (S (cPair v (codeApp (codeFreeVarTerm s) (codeFreeVarFormula (cPairPi2 (cPairPi2 input)))))) in charFunction 0 (beq_nat output (cPair 3 (cPair nv (cTriplePi2 (cPairPi2 rest)))) && (beq_nat (cTriple v s (cTriplePi2 (cPairPi1 rest))) (cTriplePi1 (cPairPi2 rest)) && beq_nat (cTriple (cPairPi1 (cPairPi2 input)) (cPair 0 nv) (cPairPi2 (cPairPi2 input))) (cTriplePi1 (cPairPi1 rest)))) * (codeNth (trace - S (cPairPi1 rest)) recs * codeNth (trace - S (cPairPi2 rest)) recs)) (charFunction 0 (beq_nat output (cPair 3 (cPair (cPairPi1 (cPairPi2 input)) (cTriplePi2 rest))) && beq_nat (cTriple v s (cPairPi2 (cPairPi2 input))) (cTriplePi1 rest)) * codeNth (trace - S rest) recs)))) (charFunction 0 (beq_nat output (cPair 2 (cTriplePi2 rest)) && beq_nat (cTriple v s (cPairPi2 input)) (cTriplePi1 rest)) * codeNth (trace - S rest) recs)) (charFunction 0 (beq_nat output (cPair 1 (cPair (cTriplePi2 (cPairPi1 rest)) (cTriplePi2 (cPairPi2 rest)))) && (beq_nat (cTriple v s (cPairPi1 (cPairPi2 input))) (cTriplePi1 (cPairPi1 rest)) && beq_nat (cTriple v s (cPairPi2 (cPairPi2 input))) (cTriplePi1 (cPairPi2 rest)))) * (codeNth (trace - S (cPairPi1 rest)) recs * codeNth (trace - S (cPairPi2 rest)) recs))) (charFunction 2 beq_nat output (cPair 0 (cPair (codeSubTerm (cPairPi1 (cPairPi2 input)) v s) (codeSubTerm (cPairPi2 (cPairPi2 input)) v s))))).
Definition makeTraceImp (f1 : fol.Formula L) (f1rec : nat * fol.Term L -> nat) (f2 : fol.Formula L) (f2rec : nat * fol.Term L -> nat) (p : nat * fol.Term L) : nat := let v := fst p in let s := snd p in cTriple (cTriple v (codeTerm s) (codeFormula (impH L f1 f2))) (codeFormula (substituteFormula L (impH L f1 f2) v s)) (cPair (f1rec p) (f2rec p)).
Definition makeTraceNot (f : fol.Formula L) (frec : nat * fol.Term L -> nat) (p : nat * fol.Term L) : nat := let v := fst p in let s := snd p in cTriple (cTriple v (codeTerm s) (codeFormula (notH L f))) (codeFormula (substituteFormula L (notH L f) v s)) (frec p).
Definition makeTraceForall (n : nat) (f : fol.Formula L) (rec : forall b : fol.Formula L, lt_depth L b (forallH L n f) -> nat * fol.Term L -> nat) (p : nat * fol.Term L) : nat.
intros.
set (v := fst p) in *.
set (s := snd p) in *.
induction (eq_nat_dec n v).
exact (cTriple (cTriple v (codeTerm s) (codeFormula (forallH L n f))) (codeFormula (substituteFormula L (forallH L n f) v s)) 0).
assert (lt_depth L f (forallH L v f)).
apply depthForall.
induction (In_dec eq_nat_dec n (freeVarTerm L s)).
set (nv := newVar (v :: freeVarTerm L s ++ freeVarFormula L f)) in *.
assert (lt_depth L (substituteFormula L f n (var nv)) (forallH L v f)).
apply eqDepth with f.
symmetry in |- *.
apply subFormulaDepth.
apply H.
exact (cTriple (cTriple v (codeTerm s) (codeFormula (forallH L n f))) (codeFormula (substituteFormula L (forallH L n f) v s)) (cPair (rec f H (n, var nv)) (rec (substituteFormula L f n (var nv)) H0 p))).
exact (cTriple (cTriple v (codeTerm s) (codeFormula (forallH L n f))) (codeFormula (substituteFormula L (forallH L n f) v s)) (rec f H p)).
Defined.
Definition makeTrace : fol.Formula L -> nat * fol.Term L -> nat := Formula_depth_rec2 L (fun _ : fol.Formula L => nat * fol.Term L -> nat) (fun (t t0 : fol.Term L) (p : nat * fol.Term L) => let v := fst p in let s := snd p in cTriple (cTriple v (codeTerm s) (codeFormula (equal L t t0))) (codeFormula (substituteFormula L (equal L t t0) v s)) 0) (fun (r : Relations L) t (p : nat * fol.Term L) => let v := fst p in let s := snd p in cTriple (cTriple v (codeTerm s) (codeFormula (atomic L r t))) (codeFormula (substituteFormula L (atomic L r t) v s)) 0) makeTraceImp makeTraceNot makeTraceForall.
Remark makeTrace1 : forall (f : fol.Formula L) (v : nat) (s : fol.Term L), cTriplePi1 (makeTrace f (v, s)) = cTriple v (codeTerm s) (codeFormula f).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; unfold makeTrace, makeTraceImp, makeTraceNot, Formula_depth_rec2, Formula_depth_rec in |- *; simpl in |- *; try (rewrite cTripleProj1; reflexivity).
unfold makeTraceForall in |- *.
induction (eq_nat_dec n (fst (v, s))); simpl in |- *.
rewrite cTripleProj1.
reflexivity.
induction (In_dec eq_nat_dec n (freeVarTerm L s)); simpl in |- *; rewrite cTripleProj1; reflexivity.
Remark makeTrace2 : forall (f : fol.Formula L) (v : nat) (s : fol.Term L), cTriplePi2 (makeTrace f (v, s)) = codeFormula (substituteFormula L f v s).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; unfold makeTrace, makeTraceImp, makeTraceNot, Formula_depth_rec2, Formula_depth_rec in |- *; simpl in |- *; try (rewrite cTripleProj2; reflexivity).
unfold makeTraceForall in |- *.
induction (eq_nat_dec n (fst (v, s))); simpl in |- *.
rewrite cTripleProj2.
reflexivity.
induction (In_dec eq_nat_dec n (freeVarTerm L s)); simpl in |- *; rewrite cTripleProj2; reflexivity.
Definition ReplaceTermTermsTerm : nat -> nat -> nat := evalStrongRec 1 (fun t recs s : nat => cPair (switchPR (cPairPi1 t) (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) (cPair 0 s)) (switchPR t (S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0)).
Remark ReplaceTermTermsTermIsPR : isPR 2 ReplaceTermTermsTerm.
Proof.
unfold ReplaceTermTermsTerm in |- *.
apply evalStrongRecIsPR.
apply compose3_2IsPR with (f1 := fun t recs s : nat => switchPR (cPairPi1 t) (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) (cPair 0 s)) (f2 := fun t recs s : nat => switchPR t (S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0).
apply compose3_3IsPR with (f1 := fun t recs s : nat => cPairPi1 t) (f2 := fun t recs s : nat => cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) (f3 := fun t recs s : nat => cPair 0 s).
apply filter100IsPR with (g := cPairPi1).
apply cPairPi1IsPR.
apply filter110IsPR with (g := fun t recs : nat => cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))).
apply compose2_2IsPR with (f := fun t recs : nat => cPairPi1 t) (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 t)) recs)).
apply filter10IsPR with (g := cPairPi1).
apply cPairPi1IsPR.
apply compose2_1IsPR with (f := fun t recs : nat => codeNth (t - S (cPairPi2 t)) recs).
apply compose2_2IsPR with (f := fun t recs : nat => t - S (cPairPi2 t)) (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (cPairPi2 t)).
apply compose1_2IsPR with (f := fun t : nat => t) (f' := fun t : nat => S (cPairPi2 t)).
apply idIsPR.
apply compose1_1IsPR.
apply cPairPi2IsPR.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
apply cPairPi2IsPR.
apply cPairIsPR.
apply filter001IsPR with (g := fun s : nat => cPair 0 s).
apply compose1_2IsPR with (f := fun s : nat => 0) (f' := fun s : nat => s).
apply const1_NIsPR.
apply idIsPR.
apply cPairIsPR.
apply switchIsPR.
apply filter110IsPR with (g := fun t recs : nat => switchPR t (S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0).
apply compose2_3IsPR with (f1 := fun t recs : nat => t) (f2 := fun t recs : nat => S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) (f3 := fun t recs : nat => 0).
apply pi1_2IsPR.
apply compose2_1IsPR with (f := fun t recs : nat => cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs))).
assert (forall g : nat -> nat, isPR 1 g -> isPR 2 (fun t recs : nat => g (codeNth (t - S (g (pred t))) recs))).
intros.
apply compose2_1IsPR with (f := fun t recs : nat => codeNth (t - S (g (pred t))) recs).
apply compose2_2IsPR with (f := fun t recs : nat => t - S (g (pred t))) (g := fun t recs : nat => recs).
apply filter10IsPR with (g := fun t : nat => t - S (g (pred t))).
apply compose1_2IsPR with (f := fun t : nat => t) (f' := fun t : nat => S (g (pred t))).
apply idIsPR.
apply compose1_1IsPR with (f := fun t : nat => g (pred t)).
apply compose1_1IsPR.
apply predIsPR.
auto.
apply succIsPR.
apply minusIsPR.
apply pi2_2IsPR.
apply codeNthIsPR.
auto.
apply compose2_2IsPR with (f := fun t recs : nat => cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (g := fun t recs : nat => cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)).
apply H.
apply cPairPi1IsPR.
apply H.
apply cPairPi2IsPR.
apply cPairIsPR.
apply succIsPR.
exists (composeFunc 2 0 (PRnil _) zeroFunc).
simpl in |- *.
auto.
apply switchIsPR.
apply cPairIsPR.
Definition ReplaceTermTerm (t s : nat) : nat := cPairPi1 (ReplaceTermTermsTerm t s).
Definition ReplaceTermsTerm (t s : nat) : nat := cPairPi2 (ReplaceTermTermsTerm t s).
Remark ReplaceTermTermsTermMonotone : forall a s1 s2 : nat, s1 <= s2 -> ReplaceTermTerm a s1 <= ReplaceTermTerm a s2 /\ ReplaceTermsTerm a s1 <= ReplaceTermsTerm a s2.
Proof.
assert (forall a s1 s2 n : nat, n < a -> s1 <= s2 -> ReplaceTermTerm n s1 <= ReplaceTermTerm n s2 /\ ReplaceTermsTerm n s1 <= ReplaceTermsTerm n s2).
intro.
unfold ReplaceTermTerm in |- *.
unfold ReplaceTermsTerm in |- *.
unfold ReplaceTermTermsTerm in |- *.
set (A := fun t recs s : nat => cPair (switchPR (cPairPi1 t) (cPair (cPairPi1 t) (cPairPi2 (codeNth (t - S (cPairPi2 t)) recs))) (cPair 0 s)) (switchPR t (S (cPair (cPairPi1 (codeNth (t - S (cPairPi1 (pred t))) recs)) (cPairPi2 (codeNth (t - S (cPairPi2 (pred t))) recs)))) 0)) in *.
induction a as [| a Hreca]; simpl in |- *; intros.
elim (lt_n_O _ H).
assert (forall n m : nat, m < n -> extEqual 1 (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _)) (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1).
assumption.
simpl in H1.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
split.
unfold A at 3 1 in |- *.
repeat rewrite cPairProjections1.
assert (cPair (cPairPi1 n) (cPairPi2 n) = n).
apply cPairProjections.
destruct (cPairPi1 n).
simpl in |- *.
apply cPairLe3.
apply le_n.
assumption.
simpl in |- *.
assert (cPairPi2 n < n).
apply lt_le_trans with (cPair (S n0) (cPairPi2 n)).
apply cPairLt2.
rewrite H2.
apply le_n.
repeat rewrite H1.
apply cPairLe3.
apply le_n.
eapply proj2.
apply Hreca.
apply lt_le_trans with n.
apply H3.
apply lt_n_Sm_le.
assumption.
assumption.
assumption.
assumption.
unfold A at 3 1 in |- *.
repeat rewrite cPairProjections2.
destruct n.
simpl in |- *.
apply le_n.
assert (cPairPi2 n < S n).
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe2.
rewrite cPairProjections.
apply le_n.
assert (cPairPi1 n < S n).
apply le_lt_n_Sm.
apply le_trans with (cPair (cPairPi1 n) (cPairPi2 n)).
apply cPairLe1.
rewrite cPairProjections.
apply le_n.
repeat rewrite H1.
simpl in |- *.
apply le_n_S.
apply cPairLe3.
eapply proj1.
apply Hreca.
apply le_lt_trans with n.
apply lt_n_Sm_le.
assumption.
apply lt_S_n.
assumption.
assumption.
eapply proj2.
apply Hreca.
apply le_lt_trans with n.
apply lt_n_Sm_le.
assumption.
apply lt_S_n.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
intros.
apply H with (S a).
apply lt_n_Sn.
assumption.
Remark maxLemma : forall a b c d : nat, a <= b -> c <= d -> max a c <= max b d.
Proof.
intros.
apply (max_case2 a c).
apply le_trans with b.
assumption.
apply le_max_l.
apply le_trans with d.
assumption.
apply le_max_r.
Remark maxLemma2 : forall a b : list nat, fold_right max 0 a <= fold_right max 0 (a ++ b).
Proof.
intros.
induction a as [| a a0 Hreca].
apply le_O_n.
simpl in |- *.
apply maxLemma.
apply le_n.
assumption.
Remark maxLemma3 : forall a b : list nat, fold_right max 0 b <= fold_right max 0 (a ++ b).
Proof.
intros.
induction a as [| a a0 Hreca].
apply le_n.
simpl in |- *.
apply le_trans with (fold_right max 0 (a0 ++ b)).
assumption.
apply le_max_r.
Remark maxApp : forall a b : list nat, {fold_right max 0 (a ++ b) = fold_right max 0 a} + {fold_right max 0 (a ++ b) = fold_right max 0 b}.
Proof.
intros.
induction a as [| a a0 Hreca].
simpl in |- *.
auto.
simpl in |- *.
induction (max_dec a (fold_right max 0 (a0 ++ b))).
rewrite a1.
left.
symmetry in |- *.
apply max_l.
apply le_trans with (max a (fold_right max 0 (a0 ++ b))).
apply le_trans with (max a (fold_right max 0 a0)).
apply le_max_r.
apply maxLemma.
apply le_n.
apply maxLemma2.
rewrite a1.
apply le_n.
induction Hreca as [a1| b1].
rewrite a1.
auto.
rewrite b0.
rewrite b1.
auto.
Definition ReplaceFormulaTerm : nat -> nat -> nat := evalStrongRec 1 (fun f recs s : nat => switchPR (cPairPi1 f) (switchPR (pred (cPairPi1 f)) (switchPR (pred (pred (cPairPi1 f))) (switchPR (pred (pred (pred (cPairPi1 f)))) (cPair (cPairPi1 f) (ReplaceTermsTerm (cPairPi2 f) s)) (cPair 3 (cPair s (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))) (cPair 2 (codeNth (f - S (cPairPi2 f)) recs))) (cPair 1 (cPair (codeNth (f - S (cPairPi1 (cPairPi2 f))) recs) (codeNth (f - S (cPairPi2 (cPairPi2 f))) recs)))) (cPair 0 (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f)) s) (ReplaceTermTerm (cPairPi2 (cPairPi2 f)) s)))).
Fixpoint varFormula (f : fol.Formula L) : list nat := match f with | equal t s => freeVarTerm L t ++ freeVarTerm L s | atomic r ts => freeVarTerms L _ ts | impH A B => varFormula A ++ varFormula B | notH A => varFormula A | forallH v A => v :: varFormula A end.
Remark codeTermFreeVar : forall s : fol.Term L, fold_right max 0 (freeVarTerm L s) <= codeTerm s.
Proof.
intros.
elim s using Term_Terms_ind with (P0 := fun (n : nat) (ts : fol.Terms L n) => fold_right max 0 (freeVarTerms L n ts) <= codeTerms L codeF n ts); simpl in |- *; intros.
apply max_case2.
unfold codeTerm in |- *.
unfold code.codeTerm in |- *.
apply cPairLe2.
apply le_O_n.
apply le_trans with (codeTerms L codeF (arity L (inr (Relations L) f)) t).
assumption.
unfold codeTerm in |- *.
unfold code.codeTerm in |- *.
apply cPairLe2.
apply le_O_n.
replace (freeVarTerms L (S n) (Tcons L n t t0)) with (freeVarTerm L t ++ freeVarTerms L n t0); [ idtac | reflexivity ].
replace (codeTerms L codeF (S n) (Tcons L n t t0)) with (S (cPair (codeTerm t) (codeTerms L codeF n t0))); [ idtac | reflexivity ].
induction (maxApp (freeVarTerm L t) (freeVarTerms L n t0)).
rewrite a.
eapply le_trans.
apply H.
apply le_S.
apply cPairLe1.
rewrite b.
eapply le_trans.
apply H0.
apply le_S.
apply cPairLe2.
Remark maxVarFreeVar : forall f : fol.Formula L, fold_right max 0 (freeVarFormula L f) <= fold_right max 0 (varFormula f).
Proof.
intros.
induction f as [t t0| r t| f1 Hrecf1 f0 Hrecf0| f Hrecf| n f Hrecf]; simpl in |- *.
apply le_n.
apply le_n.
induction (maxApp (freeVarFormula L f1) (freeVarFormula L f0)).
rewrite a.
eapply le_trans.
apply Hrecf1.
apply maxLemma2.
rewrite b.
eapply le_trans.
apply Hrecf0.
apply maxLemma3.
assumption.
apply le_trans with (fold_right max 0 (freeVarFormula L f)).
clear Hrecf.
induction (freeVarFormula L f).
simpl in |- *.
apply le_O_n.
simpl in |- *.
induction (eq_nat_dec a n).
eapply le_trans.
apply IHl.
apply le_max_r.
simpl in |- *.
apply maxLemma.
apply le_n.
assumption.
eapply le_trans.
apply Hrecf.
apply le_max_r.
Remark maxSubTerm : forall (t : fol.Term L) (v : nat) (s : fol.Term L), fold_right max 0 (freeVarTerm L (substituteTerm L t v s)) <= fold_right max 0 (freeVarTerm L s ++ freeVarTerm L t).
Proof.
intros.
elim t using Term_Terms_ind with (P0 := fun (n : nat) (ts : fol.Terms L n) => fold_right max 0 (freeVarTerms L n (substituteTerms L n ts v s)) <= fold_right max 0 (freeVarTerm L s ++ freeVarTerms L n ts)); simpl in |- *; intros.
induction (eq_nat_dec v n).
apply maxLemma2.
apply maxLemma3.
apply H.
apply le_O_n.
replace (freeVarTerms L (S n) (Tcons L n (substituteTerm L t0 v s) (substituteTerms L n t1 v s))) with (freeVarTerm L (substituteTerm L t0 v s) ++ freeVarTerms L n (substituteTerms L n t1 v s)).
replace (freeVarTerms L (S n) (Tcons L n t0 t1)) with (freeVarTerm L t0 ++ freeVarTerms L n t1).
induction (maxApp (freeVarTerm L (substituteTerm L t0 v s)) (freeVarTerms L n (substituteTerms L n t1 v s))).
rewrite a.
eapply le_trans.
apply H.
induction (maxApp (freeVarTerm L s) (freeVarTerm L t0)).
rewrite a0.
apply maxLemma2.
rewrite b.
apply le_trans with (fold_right max 0 (freeVarTerm L t0 ++ freeVarTerms L n t1)).
apply maxLemma2.
apply maxLemma3.
rewrite b.
eapply le_trans.
apply H0.
induction (maxApp (freeVarTerm L s) (freeVarTerms L n t1)).
rewrite a.
apply maxLemma2.
rewrite b0.
apply le_trans with (fold_right max 0 (freeVarTerm L t0 ++ freeVarTerms L n t1)).
apply maxLemma3.
apply maxLemma3.
reflexivity.
reflexivity.
Remark maxSubTerms : forall (n : nat) (ts : fol.Terms L n) (v : nat) (s : fol.Term L), fold_right max 0 (freeVarTerms L n (substituteTerms L n ts v s)) <= fold_right max 0 (freeVarTerm L s ++ freeVarTerms L n ts).
Proof.
intros.
induction ts as [| n t ts Hrects]; simpl in |- *; intros.
apply le_O_n.
replace (freeVarTerms L (S n) (Tcons L n (substituteTerm L t v s) (substituteTerms L n ts v s))) with (freeVarTerm L (substituteTerm L t v s) ++ freeVarTerms L n (substituteTerms L n ts v s)).
replace (freeVarTerms L (S n) (Tcons L n t ts)) with (freeVarTerm L t ++ freeVarTerms L n ts).
induction (maxApp (freeVarTerm L (substituteTerm L t v s)) (freeVarTerms L n (substituteTerms L n ts v s))).
rewrite a.
eapply le_trans.
apply maxSubTerm.
induction (maxApp (freeVarTerm L s) (freeVarTerm L t)).
rewrite a0.
apply maxLemma2.
rewrite b.
apply le_trans with (fold_right max 0 (freeVarTerm L t ++ freeVarTerms L n ts)).
apply maxLemma2.
apply maxLemma3.
rewrite b.
eapply le_trans.
apply Hrects.
induction (maxApp (freeVarTerm L s) (freeVarTerms L n ts)).
rewrite a.
apply maxLemma2.
rewrite b0.
apply le_trans with (fold_right max 0 (freeVarTerm L t ++ freeVarTerms L n ts)).
apply maxLemma3.
apply maxLemma3.
reflexivity.
reflexivity.
Definition pow3 : nat -> nat := nat_rec (fun _ => nat) 1 (fun _ rec : nat => rec + (rec + rec)).
Remark mapListLemma : forall l : list nat, fold_right max 0 (map S l) <= S (fold_right max 0 l).
Proof.
intros.
induction l as [| a l Hrecl].
simpl in |- *.
auto.
simpl in |- *.
induction (fold_right max 0 (map S l)).
apply le_n_S.
apply le_max_l.
apply le_n_S.
apply maxLemma.
apply le_n.
apply le_S_n.
assumption.
Remark boundSubFormulaHelp2 : forall (a : fol.Formula L) (v0 : nat) (s : fol.Term L), newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a) <= S (fold_right max 0 (v0 :: fold_right max 0 (freeVarTerm L s) :: varFormula a)).
intros.
unfold newVar in |- *.
apply le_trans with (S (fold_right max 0 (v0 :: freeVarTerm L s ++ freeVarFormula L a))).
apply mapListLemma.
apply le_n_S.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (freeVarFormula L a)).
rewrite a0.
apply le_max_l.
rewrite b.
eapply le_trans.
apply maxVarFreeVar.
apply le_max_r.
Remark boundSubFormulaHelp1 : forall (b a : fol.Formula L) (v0 v : nat) (s : fol.Term L), fold_right max 0 (varFormula (substituteFormula L b v (fol.var L (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a))))) <= pow3 (depth L b) + pow3 (depth L b) + max v0 (max (fold_right max 0 (freeVarTerm L s)) (max v (max (fold_right max 0 (varFormula b)) (fold_right max 0 (varFormula a))))).
Proof.
intro.
elim b using Formula_depth_ind2; intros; set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)) in *.
simpl in |- *.
apply le_S.
induction (maxApp (freeVarTerm L (substituteTerm L t v (fol.var L nv))) (freeVarTerm L (substituteTerm L t0 v (fol.var L nv)))).
rewrite a0.
eapply le_trans.
apply maxSubTerm.
simpl in |- *.
apply (max_case2 nv (fold_right max 0 (freeVarTerm L t))).
eapply le_trans.
apply (boundSubFormulaHelp2 a v0 s).
apply le_n_S.
simpl in |- *.
repeat apply maxLemma; try apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_r.
apply le_S.
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
apply maxLemma2.
rewrite b0.
eapply le_trans.
apply maxSubTerm.
simpl in |- *.
apply (max_case2 nv (fold_right max 0 (freeVarTerm L t0))).
eapply le_trans.
apply (boundSubFormulaHelp2 a v0 s).
apply le_n_S.
simpl in |- *.
repeat apply maxLemma; try apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_r.
apply le_S.
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
apply maxLemma3.
eapply le_trans.
simpl in |- *.
apply maxSubTerms.
simpl in |- *.
apply le_S.
apply (max_case2 nv (fold_right max 0 (freeVarTerms L (arity L (inl (Functions L) r)) t))).
eapply le_trans.
apply (boundSubFormulaHelp2 a v0 s).
apply le_n_S.
simpl in |- *.
repeat apply maxLemma; try apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_r.
apply le_S.
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
apply le_n.
rewrite subFormulaImp.
simpl in |- *.
induction (maxApp (varFormula (substituteFormula L f v (fol.var L nv))) (varFormula (substituteFormula L f0 v (fol.var L nv)))).
rewrite a0.
eapply le_trans.
apply (H a v0 v s).
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_l ].
assert (pow3 (depth L f) <= pow3 (max (depth L f) (depth L f0))).
apply pow3Monotone.
apply le_max_l.
apply plus_le_compat.
assumption.
eapply le_trans; [ idtac | apply le_plus_l ].
assumption.
repeat apply maxLemma; try apply le_n.
apply maxLemma2.
rewrite b0.
eapply le_trans.
apply (H0 a v0 v s).
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_l ].
assert (pow3 (depth L f0) <= pow3 (max (depth L f) (depth L f0))).
apply pow3Monotone.
apply le_max_r.
apply plus_le_compat.
assumption.
eapply le_trans; [ idtac | apply le_plus_l ].
assumption.
repeat apply maxLemma; try apply le_n.
apply maxLemma3.
rewrite subFormulaNot.
eapply le_trans.
apply (H a v0 v s).
apply plus_le_compat.
simpl in |- *.
eapply le_trans; [ idtac | apply le_plus_l ].
apply le_plus_r.
apply le_n.
clear nv.
rewrite subFormulaForall.
induction (eq_nat_dec v v1).
eapply le_trans; [ idtac | apply le_plus_r ].
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_max_l.
induction (In_dec eq_nat_dec v (freeVarTerm L (fol.var L (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))))).
simpl in |- *.
apply (max_case2 (newVar (v1 :: newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0) :: freeVarFormula L a)) (fold_right max 0 (varFormula (substituteFormula L (substituteFormula L a v (fol.var L (newVar (v1 :: newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0) :: freeVarFormula L a)))) v1 (fol.var L (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))))))).
unfold newVar at 1 in |- *.
eapply le_trans.
apply mapListLemma.
apply le_trans with (1 + 1 + max v0 (max (fold_right max 0 (freeVarTerm L s)) (max v1 (max (max v (fold_right max 0 (varFormula a))) (fold_right max 0 (varFormula a0)))))).
simpl in |- *.
apply le_n_S.
apply (max_case2 v1 (max (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0)) (fold_right max 0 (freeVarFormula L a)))).
apply le_S.
do 2 (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_max_l.
apply (max_case2 (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0)) (fold_right max 0 (freeVarFormula L a))).
eapply le_trans.
apply boundSubFormulaHelp2.
apply le_n_S.
simpl in |- *.
repeat apply maxLemma; try apply le_n.
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_r.
apply le_S.
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
eapply le_trans.
apply maxVarFreeVar.
apply le_max_r.
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_r ].
apply plus_le_compat.
apply pow3Min.
simpl in |- *.
eapply le_trans; [ idtac | apply le_plus_r ].
apply pow3Min.
apply le_n.
eapply le_trans.
apply H.
eapply eqDepth.
symmetry in |- *.
apply subFormulaDepth.
apply depthForall.
rewrite subFormulaDepth.
rewrite (plus_assoc (pow3 (depth L a)) (pow3 (depth L a)) (pow3 (depth L a))).
repeat rewrite (plus_assoc_reverse (pow3 (depth L a) + pow3 (depth L a))).
apply plus_le_compat.
apply le_n.
apply (max_case2 v0 (max (fold_right max 0 (freeVarTerm L s)) (max v1 (max (fold_right max 0 (varFormula (substituteFormula L a v (fol.var L (newVar (v1 :: newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0) :: freeVarFormula L a)))))) (fold_right max 0 (varFormula a0)))))).
eapply le_trans; [ idtac | apply le_plus_r ].
apply le_max_l.
apply (max_case2 (fold_right max 0 (freeVarTerm L s)) (max v1 (max (fold_right max 0 (varFormula (substituteFormula L a v (fol.var L (newVar (v1 :: newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0) :: freeVarFormula L a)))))) (fold_right max 0 (varFormula a0))))).
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
apply le_max_l.
apply (max_case2 v1 (max (fold_right max 0 (varFormula (substituteFormula L a v (fol.var L (newVar (v1 :: newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0) :: freeVarFormula L a)))))) (fold_right max 0 (varFormula a0)))).
eapply le_trans; [ idtac | apply le_plus_r ].
do 2 (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_max_l.
apply (max_case2 (fold_right max 0 (varFormula (substituteFormula L a v (fol.var L (newVar (v1 :: newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0) :: freeVarFormula L a)))))) (fold_right max 0 (varFormula a0))).
eapply le_trans.
apply H with (b := a) (v := v) (v0 := v1) (a := a) (s := var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))).
apply depthForall.
rewrite (plus_comm (pow3 (depth L a)) (pow3 (depth L a) + pow3 (depth L a) + pow3 (depth L a))) .
repeat rewrite (plus_assoc_reverse (pow3 (depth L a) + pow3 (depth L a))).
apply plus_le_compat.
apply le_n.
apply (max_case2 v1 (max (fold_right max 0 (freeVarTerm L (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))))) (max v (max (fold_right max 0 (varFormula a)) (fold_right max 0 (varFormula a)))))).
eapply le_trans; [ idtac | apply le_plus_r ].
do 2 (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_max_l.
apply (max_case2 (fold_right max 0 (freeVarTerm L (var (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))))) (max v (max (fold_right max 0 (varFormula a)) (fold_right max 0 (varFormula a))))).
simpl in |- *.
apply (max_case2 (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0)) 0).
eapply le_trans.
apply boundSubFormulaHelp2.
apply le_trans with (1 + max v0 (max (fold_right max 0 (freeVarTerm L s)) (max v1 (max (max v (fold_right max 0 (varFormula a))) (fold_right max 0 (varFormula a0)))))).
simpl in |- *.
apply le_n_S.
repeat apply maxLemma; try apply le_n.
repeat (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_n.
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_r ].
apply pow3Min.
apply le_n.
apply le_O_n.
eapply le_trans; [ idtac | apply le_plus_r ].
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
apply (max_case2 v (max (fold_right max 0 (varFormula a)) (fold_right max 0 (varFormula a)))).
eapply le_trans; [ idtac | apply le_max_l ].
apply le_max_l.
apply (max_case2 (fold_right max 0 (varFormula a)) (fold_right max 0 (varFormula a))); (eapply le_trans; [ idtac | apply le_max_l ]; apply le_max_r).
eapply le_trans; [ idtac | apply le_plus_r ].
repeat (eapply le_trans; [ idtac | apply le_max_r ]).
apply le_n.
simpl in |- *.
apply (max_case2 v (fold_right max 0 (varFormula (substituteFormula L a v1 (fol.var L (newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a0))))))).
eapply le_trans; [ idtac | apply le_plus_r ].
do 3 (eapply le_trans; [ idtac | apply le_max_r ]).
eapply le_trans; [ idtac | apply le_max_l ].
apply le_max_l.
eapply le_trans.
apply H.
apply depthForall.
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_r ].
apply plus_le_compat.
apply le_n.
apply le_plus_l.
repeat apply maxLemma; try apply le_n.
apply le_max_r.
Remark boundSubFormulaHelp : forall (f : fol.Formula L) (v : nat) (s : fol.Term L), codeFormula (substituteFormula L f v s) <= ReplaceFormulaTerm (codeFormula f) (max (codeTerm s) (pow3 (depth L f) + fold_right max 0 (v :: freeVarTerm L s ++ varFormula f))).
Proof.
intro.
unfold ReplaceFormulaTerm in |- *.
set (A := fun f0 recs s0 : nat => switchPR (cPairPi1 f0) (switchPR (pred (cPairPi1 f0)) (switchPR (pred (pred (cPairPi1 f0))) (switchPR (pred (pred (pred (cPairPi1 f0)))) (cPair (cPairPi1 f0) (ReplaceTermsTerm (cPairPi2 f0) s0)) (cPair 3 (cPair s0 (codeNth (f0 - S (cPairPi2 (cPairPi2 f0))) recs)))) (cPair 2 (codeNth (f0 - S (cPairPi2 f0)) recs))) (cPair 1 (cPair (codeNth (f0 - S (cPairPi1 (cPairPi2 f0))) recs) (codeNth (f0 - S (cPairPi2 (cPairPi2 f0))) recs)))) (cPair 0 (cPair (ReplaceTermTerm (cPairPi1 (cPairPi2 f0)) s0) (ReplaceTermTerm (cPairPi2 (cPairPi2 f0)) s0)))) in *.
assert (forall n m : nat, m < n -> extEqual 1 (evalComposeFunc 1 1 (Vector.cons _ (evalStrongRecHelp 1 A n) 0 (Vector.nil _)) (fun b : nat => codeNth (n - S m) b)) (evalStrongRec 1 A m)).
intros.
apply (evalStrongRecHelp2 1).
assumption.
simpl in H.
elim f using Formula_depth_ind2; intros.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
set (C := max (codeTerm s) (pow3 (depth L (equal L t t0)) + fold_right max 0 (v :: freeVarTerm L s ++ varFormula (equal L t t0)))) in *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
apply le_trans with (ReplaceTermTerm (codeTerm t) (fold_right max 0 (codeTerm s :: freeVarTerm L t))).
apply boundSubTerm.
apply ReplaceTermTermMonotone.
unfold C in |- *.
simpl in |- *.
apply maxLemma.
apply le_n.
apply le_S.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
apply maxLemma2.
apply le_trans with (ReplaceTermTerm (codeTerm t0) (fold_right max 0 (codeTerm s :: freeVarTerm L t0))).
apply boundSubTerm.
apply ReplaceTermTermMonotone.
unfold C in |- *.
simpl in |- *.
apply maxLemma.
apply le_n.
apply le_S.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
apply maxLemma3.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
set (C := max (codeTerm s) (pow3 (depth L (atomic L r t)) + fold_right max 0 (v :: freeVarTerm L s ++ varFormula (atomic L r t)))) in *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
simpl in |- *.
apply cPairLe3.
apply le_n.
apply le_trans with (ReplaceTermsTerm (codeTerms L codeF _ t) (fold_right max 0 (codeTerm s :: freeVarTerms L _ t))).
apply boundSubTerms.
apply ReplaceTermsTermMonotone.
unfold C in |- *.
simpl in |- *.
apply maxLemma.
apply le_n.
apply le_S.
eapply le_trans; [ idtac | apply le_max_r ].
apply maxLemma3.
rewrite subFormulaImp.
set (C := max (codeTerm s) (pow3 (depth L (impH L f0 f1)) + fold_right max 0 (v :: freeVarTerm L s ++ varFormula (impH L f0 f1)))) in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula f0).
rewrite H with (m := codeFormula f1).
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
apply le_trans with (evalStrongRec 1 A (codeFormula f0) (max (codeTerm s) (pow3 (depth L f0) + fold_right max 0 (v :: freeVarTerm L s ++ varFormula f0)))).
auto.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_S.
apply le_max_l.
simpl in |- *.
apply maxLemma.
apply le_n.
rewrite ass_app.
apply maxLemma2.
apply le_trans with (evalStrongRec 1 A (codeFormula f1) (max (codeTerm s) (pow3 (depth L f1) + fold_right max 0 (v :: freeVarTerm L s ++ varFormula f1)))).
auto.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_S.
apply le_max_r.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (varFormula f1)).
rewrite a.
apply maxLemma2.
rewrite b.
eapply le_trans; [ idtac | apply maxLemma3 ].
apply maxLemma3.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe1.
rewrite subFormulaNot.
set (C := max (codeTerm s) (pow3 (depth L (notH L f0)) + fold_right max 0 (v :: freeVarTerm L s ++ varFormula (notH L f0)))) in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula f0).
simpl in |- *.
apply cPairLe3.
apply le_n.
apply le_trans with (evalStrongRec 1 A (codeFormula f0) (max (codeTerm s) (pow3 (depth L f0) + fold_right max 0 (v :: freeVarTerm L s ++ varFormula f0)))).
auto.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_n_Sn.
apply le_n.
apply cPairLt2.
set (C := max (codeTerm s) (pow3 (depth L (forallH L v a)) + fold_right max 0 (v0 :: freeVarTerm L s ++ varFormula (forallH L v a)))) in *.
unfold evalStrongRec in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
repeat rewrite computeEvalStrongRecHelp.
unfold compose2 in |- *.
unfold evalComposeFunc, evalOneParamList, evalList in |- *.
simpl in |- *.
repeat rewrite cPairProjections1.
unfold A at 1 in |- *.
repeat first [ rewrite cPairProjections1 | rewrite cPairProjections2 ].
rewrite H with (m := codeFormula a).
simpl in |- *.
rewrite subFormulaForall.
induction (eq_nat_dec v v0).
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
unfold C in |- *.
rewrite a0.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply le_plus_r ].
simpl in |- *.
apply le_max_l.
apply le_trans with (codeFormula (substituteFormula L a 0 (var 0))).
rewrite (subFormulaId L).
apply le_n.
apply le_trans with (evalStrongRec 1 A (codeFormula a) (max (codeTerm (var 0)) (pow3 (depth L a) + fold_right max 0 (0 :: freeVarTerm L (var 0) ++ varFormula a)))).
apply H0.
apply depthForall.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_O_n.
apply plus_le_compat.
apply pow3Monotone.
simpl in |- *.
apply le_n_Sn.
simpl in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_r.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
simpl in |- *.
apply cPairLe3.
apply le_n.
set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)) in *.
apply cPairLe3.
unfold C in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
simpl in |- *.
apply le_trans with (1 + max v0 (fold_right max 0 (freeVarTerm L s ++ v :: varFormula a))).
simpl in |- *.
unfold nv in |- *.
unfold newVar in |- *.
eapply le_trans.
apply mapListLemma.
apply le_n_S.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (freeVarFormula L a)).
rewrite a1.
apply maxLemma2.
rewrite b0.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
apply maxVarFreeVar.
apply plus_le_compat.
eapply le_trans; [ idtac | apply le_plus_l ].
apply pow3Min.
apply le_n.
set (B := substituteFormula L a v (fol.var L nv)) in *.
apply le_trans with (evalStrongRec 1 A (codeFormula B) (max (codeTerm s) (pow3 (depth L B) + fold_right max 0 (v0 :: freeVarTerm L s ++ varFormula B)))).
apply H0.
unfold B in |- *.
eapply eqDepth.
symmetry in |- *.
apply subFormulaDepth.
apply depthForall.
unfold B at 1 in |- *.
rewrite ReplaceFormulaTermSub.
apply ReplaceFormulaTermMonotone.
simpl in |- *.
unfold B at 1 2 in |- *.
rewrite subFormulaDepth.
unfold C in |- *.
simpl in |- *.
apply maxLemma.
apply le_n.
rewrite plus_assoc_reverse.
apply plus_le_compat_l.
apply (max_case2 v0 (fold_right max 0 (freeVarTerm L s ++ varFormula (substituteFormula L a v (fol.var L nv))))).
eapply le_trans; [ idtac | apply le_plus_r ].
apply le_max_l.
induction (maxApp (freeVarTerm L s) (varFormula (substituteFormula L a v (fol.var L nv)))).
rewrite a1.
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
apply maxLemma2.
rewrite b0; clear b0.
clear H0 C B.
unfold nv in |- *.
clear nv.
eapply le_trans.
apply boundSubFormulaHelp1.
apply plus_le_compat.
apply le_n.
repeat apply maxLemma.
apply le_n.
apply max_case2.
apply maxLemma2.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply maxLemma.
apply le_n.
apply max_case2; apply le_n.
simpl in |- *.
apply cPairLe3.
apply le_n.
apply cPairLe3.
unfold C in |- *.
simpl in |- *.
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply le_plus_r ].
eapply le_trans; [ idtac | apply le_max_r ].
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_l.
eapply le_trans.
apply H0.
apply depthForall.
apply ReplaceFormulaTermMonotone.
unfold C in |- *.
apply maxLemma.
apply le_n.
apply plus_le_compat.
simpl in |- *.
apply le_plus_l.
simpl in |- *.
apply maxLemma.
apply le_n.
induction (maxApp (freeVarTerm L s) (varFormula a)).
rewrite a0.
apply maxLemma2.
rewrite b1.
eapply le_trans; [ idtac | apply maxLemma3 ].
simpl in |- *.
apply le_max_r.
eapply le_lt_trans; [ idtac | apply cPairLt2 ].
apply cPairLe2.
Definition boundComputation (d p1 p2 : nat) : nat := nat_rec (fun _ => nat) (cTriple p1 p2 0) (fun _ rec : nat => cTriple p1 p2 (cPair rec rec)) d.
Definition codeSubFormula (f v s : nat) : nat := let C := cPair 0 (pow3 f + (v + (s + f))) in cPairPi1 (boundedSearch (fun p x : nat => ltBool 0 (checkSubFormulaTrace (cPair (cPairPi1 p) x))) (cPair (cTriple v s f) (S (boundComputation f (cTriple C C (ReplaceFormulaTerm f C)) (ReplaceFormulaTerm f C))))).
End Code_Substitute_Formula.

Lemma ReplaceTermsTermMonotone : forall a s1 s2 : nat, s1 <= s2 -> ReplaceTermsTerm a s1 <= ReplaceTermsTerm a s2.
Proof.
intros.
eapply proj2.
apply ReplaceTermTermsTermMonotone.
assumption.

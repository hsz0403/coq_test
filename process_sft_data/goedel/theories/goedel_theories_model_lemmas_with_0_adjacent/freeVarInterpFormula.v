Require Import Ensembles.
Require Import Coq.Lists.List.
Require Import ListExt.
Require Import folProof.
Require Import folProp.
Require Vector.
Require Import Peano_dec.
Require Import misc.
Require Import Arith.
Section Model_Theory.
Variable L : Language.
Fixpoint naryFunc (A : Set) (n : nat) {struct n} : Set := match n with | O => A | S m => A -> naryFunc A m end.
Fixpoint naryRel (A : Set) (n : nat) {struct n} : Type := match n with | O => Prop | S m => A -> naryRel A m end.
Record Model : Type := model {U : Set; func : forall f : Functions L, naryFunc U (arity L (inr _ f)); rel : forall r : Relations L, naryRel U (arity L (inl _ r))}.
Variable M : Model.
Fixpoint interpTerm (value : nat -> U M) (t : Term L) {struct t} : U M := match t with | var v => value v | apply f ts => interpTerms _ (func M f) value ts end with interpTerms (m : nat) (f : naryFunc (U M) m) (value : nat -> U M) (ts : Terms L m) {struct ts} : U M := match ts in (Terms _ n) return (naryFunc (U M) n -> U M) with | Tnil => fun f => f | Tcons m t ts => fun f => interpTerms m (f (interpTerm value t)) value ts end f.
Fixpoint interpRels (m : nat) (r : naryRel (U M) m) (value : nat -> U M) (ts : Terms L m) {struct ts} : Prop := match ts in (Terms _ n) return (naryRel (U M) n -> Prop) with | Tnil => fun r => r | Tcons m t ts => fun r => interpRels m (r (interpTerm value t)) value ts end r.
Definition updateValue (value : nat -> U M) (n : nat) (v : U M) (x : nat) : U M := match eq_nat_dec n x with | left _ => v | right _ => value x end.
Fixpoint interpFormula (value : nat -> U M) (f : Formula L) {struct f} : Prop := match f with | equal t s => interpTerm value t = interpTerm value s | atomic r ts => interpRels _ (rel M r) value ts | impH A B => interpFormula value A -> interpFormula value B | notH A => interpFormula value A -> False | forallH v A => forall x : U M, interpFormula (updateValue value v x) A end.
Fixpoint nnHelp (f : Formula L) : Formula L := match f with | equal t s => equal L t s | atomic r ts => atomic L r ts | impH A B => impH L (nnHelp A) (nnHelp B) | notH A => notH L (nnHelp A) | forallH v A => forallH L v (notH L (notH L (nnHelp A))) end.
Definition nnTranslate (f : Formula L) : Formula L := notH L (notH L (nnHelp f)).
Section Consistent_Theory.
Variable T : System L.
Fixpoint interpTermsVector (value : nat -> U M) (n : nat) (ts : Terms L n) {struct ts} : Vector.t (U M) n := match ts in (Terms _ n) return (Vector.t (U M) n) with | Tnil => Vector.nil (U M) | Tcons m t ts => Vector.cons (U M) (interpTerm value t) m (interpTermsVector value m ts) end.
End Consistent_Theory.
End Model_Theory.

Lemma freeVarInterpFormula : forall (v1 v2 : nat -> U M) (g : Formula L), (forall x : nat, In x (freeVarFormula L g) -> v1 x = v2 x) -> interpFormula v1 g -> interpFormula v2 g.
Proof.
intros v1 v2 g.
generalize v1 v2.
clear v1 v2.
induction g as [t t0| r t| g1 Hrecg1 g0 Hrecg0| g Hrecg| n g Hrecg]; simpl in |- *; intros v1 v2 H.
repeat rewrite (freeVarInterpTerm v1 v2).
auto.
intros.
apply H.
simpl in |- *.
auto with datatypes.
intros.
apply H.
simpl in |- *.
auto with datatypes.
intros.
apply (freeVarInterpRel v1 v2).
apply H.
apply H0.
assert (interpFormula v2 g1 -> interpFormula v1 g1).
apply Hrecg1.
intros.
symmetry in |- *.
apply H.
simpl in |- *.
auto with datatypes.
assert (interpFormula v1 g0 -> interpFormula v2 g0).
apply Hrecg0.
intros.
apply H.
simpl in |- *.
auto with datatypes.
tauto.
intros.
apply H0.
apply Hrecg with v2.
intros.
symmetry in |- *.
auto.
assumption.
intros.
apply Hrecg with (updateValue v1 n x).
intros.
unfold updateValue in |- *.
induction (eq_nat_dec n x0).
reflexivity.
apply H.
apply In_list_remove3; auto.
auto.

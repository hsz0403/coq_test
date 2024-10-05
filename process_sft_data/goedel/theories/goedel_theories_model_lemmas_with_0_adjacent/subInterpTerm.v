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

Lemma subInterpTerm : forall (value : nat -> U M) (t : Term L) (v : nat) (s : Term L), interpTerm (updateValue value v (interpTerm value s)) t = interpTerm value (substituteTerm L t v s).
Proof.
intros.
elim t using Term_Terms_ind with (P0 := fun (n : nat) (ts : Terms L n) => forall f : naryFunc (U M) n, interpTerms n f (updateValue value v (interpTerm value s)) ts = interpTerms n f value (substituteTerms L n ts v s)); simpl in |- *; intros.
unfold updateValue in |- *.
induction (eq_nat_dec v n); reflexivity.
rewrite H.
reflexivity.
reflexivity.
rewrite H.
apply H0.

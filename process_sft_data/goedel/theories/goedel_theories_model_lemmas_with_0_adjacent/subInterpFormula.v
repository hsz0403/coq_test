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

Lemma subInterpFormula : forall (value : nat -> U M) (f : Formula L) (v : nat) (s : Term L), interpFormula (updateValue value v (interpTerm value s)) f <-> interpFormula value (substituteFormula L f v s).
Proof.
intros value f.
generalize value.
clear value.
elim f using Formula_depth_ind2; simpl in |- *; intros.
repeat rewrite subInterpTerm.
tauto.
apply subInterpRel.
rewrite (subFormulaImp L).
simpl in |- *.
assert (interpFormula (updateValue value v (interpTerm value s)) f1 <-> interpFormula value (substituteFormula L f1 v s)).
auto.
assert (interpFormula (updateValue value v (interpTerm value s)) f0 <-> interpFormula value (substituteFormula L f0 v s)).
auto.
tauto.
rewrite (subFormulaNot L).
simpl in |- *.
assert (interpFormula (updateValue value v (interpTerm value s)) f0 <-> interpFormula value (substituteFormula L f0 v s)).
auto.
tauto.
rewrite (subFormulaForall L).
induction (eq_nat_dec v v0).
rewrite a0.
simpl in |- *.
unfold updateValue in |- *.
split.
intros.
apply freeVarInterpFormula with (fun x0 : nat => match eq_nat_dec v0 x0 with | left _ => x | right _ => match eq_nat_dec v0 x0 with | left _ => interpTerm value s | right _ => value x0 end end).
intros.
induction (eq_nat_dec v0 x0); reflexivity.
auto.
intros.
apply freeVarInterpFormula with (fun x0 : nat => match eq_nat_dec v0 x0 with | left _ => x | right _ => value x0 end).
intros.
induction (eq_nat_dec v0 x0); reflexivity.
auto.
induction (In_dec eq_nat_dec v (freeVarTerm L s)).
simpl in |- *.
set (nv := newVar (v0 :: freeVarTerm L s ++ freeVarFormula L a)) in *.
assert (~ In nv (v0 :: freeVarTerm L s ++ freeVarFormula L a)).
unfold nv in |- *.
apply newVar1.
assert (forall (x : U M) (x0 : nat), In x0 (freeVarFormula L a) -> updateValue (updateValue value v0 (interpTerm value s)) v x x0 = updateValue (updateValue (updateValue value nv x) v0 (interpTerm (updateValue value nv x) s)) v (interpTerm (updateValue (updateValue value nv x) v0 (interpTerm (updateValue value nv x) s)) (var L nv)) x0).
intros.
unfold updateValue in |- *.
simpl in |- *.
induction (eq_nat_dec v x0).
induction (eq_nat_dec v0 nv).
elim H0.
rewrite a2.
simpl in |- *.
auto.
induction (eq_nat_dec nv nv).
reflexivity.
elim b1.
reflexivity.
induction (eq_nat_dec v0 x0).
apply freeVarInterpTerm.
intros.
induction (eq_nat_dec nv x1).
elim H0.
rewrite a2.
simpl in |- *.
auto with datatypes.
reflexivity.
induction (eq_nat_dec nv x0).
elim H0.
rewrite a1.
auto with datatypes.
reflexivity.
assert ((forall x : U M, interpFormula (updateValue (updateValue (updateValue value nv x) v0 (interpTerm (updateValue value nv x) s)) v (interpTerm (updateValue (updateValue value nv x) v0 (interpTerm (updateValue value nv x) s)) (var L nv))) a) <-> (forall x : U M, interpFormula (updateValue value nv x) (substituteFormula L (substituteFormula L a v (var L nv)) v0 s))).
split.
assert (forall b : Formula L, lt_depth L b (forallH L v a) -> forall (value : nat -> U M) (v : nat) (s : Term L), interpFormula (updateValue value v (interpTerm value s)) b -> interpFormula value (substituteFormula L b v s)).
intros.
induction (H b0 H2 value0 v1 s0).
auto.
intros.
apply H2.
eapply eqDepth.
symmetry in |- *.
apply subFormulaDepth.
apply depthForall.
apply H2.
apply depthForall.
apply H3.
intros.
assert (forall b : Formula L, lt_depth L b (forallH L v a) -> forall (value : nat -> U M) (v : nat) (s : Term L), interpFormula value (substituteFormula L b v s) -> interpFormula (updateValue value v (interpTerm value s)) b).
intros.
induction (H b0 H3 value0 v1 s0).
auto.
clear H.
intros.
apply H3.
apply depthForall.
apply H3.
eapply eqDepth.
symmetry in |- *.
apply subFormulaDepth.
apply depthForall.
auto.
assert ((forall x : U M, interpFormula (updateValue (updateValue value v0 (interpTerm value s)) v x) a) <-> (forall x : U M, interpFormula (updateValue (updateValue (updateValue value nv x) v0 (interpTerm (updateValue value nv x) s)) v (interpTerm (updateValue (updateValue value nv x) v0 (interpTerm (updateValue value nv x) s)) (var L nv))) a)).
split.
intros.
apply freeVarInterpFormula with (updateValue (updateValue value v0 (interpTerm value s)) v x).
auto.
auto.
intros.
apply freeVarInterpFormula with (updateValue (updateValue (updateValue value nv x) v0 (interpTerm (updateValue value nv x) s)) v (interpTerm (updateValue (updateValue value nv x) v0 (interpTerm (updateValue value nv x) s)) (var L nv))).
intros.
symmetry in |- *.
auto.
auto.
tauto.
simpl in |- *.
assert (forall (x : U M) (x0 : nat), In x0 (freeVarFormula L a) -> updateValue (updateValue value v0 (interpTerm value s)) v x x0 = updateValue (updateValue value v x) v0 (interpTerm (updateValue value v x) s) x0).
intros.
unfold updateValue in |- *.
induction (eq_nat_dec v x0).
induction (eq_nat_dec v0 x0).
elim b.
transitivity x0; auto.
reflexivity.
induction (eq_nat_dec v0 x0).
apply freeVarInterpTerm.
intros.
induction (eq_nat_dec v x1).
elim b0.
rewrite a1.
auto.
reflexivity.
reflexivity.
split.
intros.
assert (forall b : Formula L, lt_depth L b (forallH L v a) -> forall (value : nat -> U M) (v : nat) (s : Term L), interpFormula (updateValue value v (interpTerm value s)) b -> interpFormula value (substituteFormula L b v s)).
intros.
induction (H b1 H2 value0 v1 s0).
auto.
apply H2.
apply depthForall.
apply freeVarInterpFormula with (updateValue (updateValue value v0 (interpTerm value s)) v x).
apply (H0 x).
apply H1.
assert (forall b : Formula L, lt_depth L b (forallH L v a) -> forall (value : nat -> U M) (v : nat) (s : Term L), interpFormula value (substituteFormula L b v s) -> interpFormula (updateValue value v (interpTerm value s)) b).
intros.
induction (H b1 H1 value0 v1 s0).
auto.
intros.
apply freeVarInterpFormula with (updateValue (updateValue value v x) v0 (interpTerm (updateValue value v x) s)).
intros.
symmetry in |- *.
auto.
apply H1.
apply depthForall.
auto.

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

Lemma preserveValue : forall value : nat -> U M, (forall f : Formula L, mem _ T f -> interpFormula value (nnTranslate f)) -> forall g : Formula L, SysPrf L T g -> interpFormula value (nnTranslate g).
Proof.
intros.
induction H0 as (x, H0).
induction H0 as (x0, H0).
cut (forall g : Formula L, In g x -> interpFormula value (nnTranslate g)).
clear H H0.
generalize value.
clear value.
induction x0 as [A| Axm1 Axm2 A B x0_1 Hrecx0_1 x0_0 Hrecx0_0| Axm A v n x0 Hrecx0| A B| A B C| A B| A v t| A v n| A B v| | | | R| f]; intros; try (simpl in |- *; tauto).
apply H.
auto with datatypes.
assert (interpFormula value (nnTranslate A)).
auto with datatypes.
assert (interpFormula value (nnTranslate (impH L A B))).
auto with datatypes.
clear Hrecx0_1 Hrecx0_0.
simpl in H0.
simpl in H1.
simpl in |- *.
tauto.
simpl in |- *.
intros.
apply H0.
clear H0.
intros.
simpl in Hrecx0.
apply (Hrecx0 (updateValue value v x)).
intros.
simpl in H.
eapply H.
apply H1.
intros.
apply H2.
apply freeVarInterpFormula with value.
intros.
rewrite <- freeVarNNHelp in H4.
unfold updateValue in |- *.
induction (eq_nat_dec v x1).
elim n.
rewrite a.
clear n x0 Hrecx0 H.
induction Axm as [| a0 Axm HrecAxm].
apply H1.
simpl in |- *.
simpl in H1.
induction H1 as [H| H].
rewrite H.
auto with datatypes.
auto with datatypes.
reflexivity.
assumption.
assumption.
simpl in |- *.
intros.
apply H0.
intros.
elim H1 with (interpTerm value t).
intros.
apply H0.
intros.
rewrite <- subNNHelp.
apply subInterpFormula1.
auto.
simpl in |- *.
intros.
apply H0.
intros.
apply H2.
apply freeVarInterpFormula with value.
intros.
unfold updateValue in |- *.
induction (eq_nat_dec v x0).
elim n.
rewrite a.
rewrite freeVarNNHelp.
assumption.
reflexivity.
assumption.
simpl in |- *.
intros.
apply H0.
clear H0.
intros.
apply H0 with x.
intros.
apply H1 with x.
auto.
simpl in |- *.
auto.
simpl in |- *.
intros.
apply H0.
intros.
transitivity (value 1); auto.
simpl in |- *.
intros.
apply H0.
clear H H0.
unfold AxmEq4 in |- *.
cut (forall a b : Terms L (arity L (inl (Functions L) R)), interpTermsVector value _ a = interpTermsVector value _ b -> interpFormula value (nnHelp (iffH L (atomic L R a) (atomic L R b)))).
assert (forall A, (forall a b : Terms L (arity L (inl (Functions L) R)), interpTermsVector value (arity L (inl (Functions L) R)) a = interpTermsVector value (arity L (inl (Functions L) R)) b -> interpFormula value (nnHelp (A a b))) -> interpFormula value (nnHelp (nat_rec (fun _ : nat => Formula L) (prod_rec (fun _ : Terms L (arity L (inl (Functions L) R)) * Terms L (arity L (inl (Functions L) R)) => Formula L) (fun a b : Terms L (arity L (inl (Functions L) R)) => A a b) (nVars L (arity L (inl (Functions L) R)))) (fun (n : nat) (Hrecn : Formula L) => impH L (equal L (var L (n + n)) (var L (S (n + n)))) Hrecn) (arity L (inl (Functions L) R))))).
generalize (arity L (inl (Functions L) R)).
simple induction n.
simpl in |- *.
intros.
apply H.
reflexivity.
intros.
simpl in |- *.
induction (nVars L n0).
simpl in |- *.
simpl in H.
intros.
apply (H (fun x y : Terms L n0 => A (Tcons L n0 (var L (n0 + n0)) x) (Tcons L n0 (var L (S (n0 + n0))) y))).
intros.
apply H0.
simpl in |- *.
rewrite H1.
rewrite H2.
reflexivity.
apply (H (fun a b => iffH L (atomic L R a) (atomic L R b))).
simpl in |- *.
generalize (rel M R).
generalize (arity L (inl (Functions L) R)).
intros.
induction a as [| n t a Hreca].
assert (b = Tnil L).
symmetry in |- *.
apply nilTerms.
rewrite H1 in H0.
auto.
induction (consTerms L n b).
induction x as (a0, b0).
simpl in p.
rewrite <- p in H0.
rewrite <- p in H.
simpl in H.
inversion H.
simpl in H0.
rewrite H2 in H0.
apply (Hreca (n0 (interpTerm value a0)) b0).
apply (inj_right_pair2 _ eq_nat_dec _ _ _ _ H3).
auto.
simpl in |- *.
intros.
apply H0.
clear H H0.
unfold AxmEq5 in |- *.
cut (forall a b : Terms L (arity L (inr (Relations L) f)), interpTermsVector value _ a = interpTermsVector value _ b -> interpFormula value (nnHelp (equal L (apply L f a) (apply L f b)))).
assert (forall A, (forall a b : Terms L (arity L (inr (Relations L) f)), interpTermsVector value (arity L (inr (Relations L) f)) a = interpTermsVector value (arity L (inr (Relations L) f)) b -> interpFormula value (nnHelp (A a b))) -> interpFormula value (nnHelp (nat_rec (fun _ : nat => Formula L) (prod_rec (fun _ : Terms L (arity L (inr (Relations L) f)) * Terms L (arity L (inr (Relations L) f)) => Formula L) (fun a b : Terms L (arity L (inr (Relations L) f)) => A a b) (nVars L (arity L (inr (Relations L) f)))) (fun (n : nat) (Hrecn : Formula L) => impH L (equal L (var L (n + n)) (var L (S (n + n)))) Hrecn) (arity L (inr (Relations L) f))))).
generalize (arity L (inr (Relations L) f)).
simple induction n.
simpl in |- *.
intros.
auto.
intros.
simpl in |- *.
induction (nVars L n0).
simpl in |- *.
simpl in H.
intros.
apply (H (fun x y : Terms L n0 => A (Tcons L n0 (var L (n0 + n0)) x) (Tcons L n0 (var L (S (n0 + n0))) y))).
intros.
apply H0.
simpl in |- *.
rewrite H1.
rewrite H2.
reflexivity.
apply (H (fun a b => equal L (apply L f a) (apply L f b))).
simpl in |- *.
generalize (func M f).
generalize (arity L (inr (Relations L) f)).
intros.
induction a as [| n t a Hreca].
assert (b = Tnil L).
symmetry in |- *.
apply nilTerms.
rewrite H0.
reflexivity.
induction (consTerms L n b).
induction x as (a0, b0).
simpl in p.
rewrite <- p.
rewrite <- p in H.
simpl in H.
inversion H.
simpl in |- *.
rewrite H1.
apply Hreca.
apply (inj_right_pair2 _ eq_nat_dec _ _ _ _ H2).
auto.

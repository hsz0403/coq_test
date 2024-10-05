Require Import Coq.Lists.List.
Require Import Ensembles.
Require Import Peano_dec.
Require Import Eqdep_dec.
Require Import Arith.
Require Import Compare_dec.
Require Import Max.
Require Import misc.
Unset Standard Proposition Elimination Names.
Record Language : Type := language {Relations : Set; Functions : Set; arity : Relations + Functions -> nat}.
Section First_Order_Logic.
Variable L : Language.
Inductive Term : Set := | var : nat -> Term | apply : forall f : Functions L, Terms (arity L (inr _ f)) -> Term with Terms : nat -> Set := | Tnil : Terms 0 | Tcons : forall n : nat, Term -> Terms n -> Terms (S n).
Scheme Term_Terms_ind := Induction for Term Sort Prop with Terms_Term_ind := Induction for Terms Sort Prop.
Scheme Term_Terms_rec := Minimality for Term Sort Set with Terms_Term_rec := Minimality for Terms Sort Set.
Scheme Term_Terms_rec_full := Induction for Term Sort Set with Terms_Term_rec_full := Induction for Terms Sort Set.
Inductive Formula : Set := | equal : Term -> Term -> Formula | atomic : forall r : Relations L, Terms (arity L (inl _ r)) -> Formula | impH : Formula -> Formula -> Formula | notH : Formula -> Formula | forallH : nat -> Formula -> Formula.
Definition Formulas := list Formula.
Definition System := Ensemble Formula.
Definition mem := Ensembles.In.
Section Fol_Full.
Definition orH (A B : Formula) := impH (notH A) B.
Definition andH (A B : Formula) := notH (orH (notH A) (notH B)).
Definition iffH (A B : Formula) := andH (impH A B) (impH B A).
Definition existH (x : nat) (A : Formula) := notH (forallH x (notH A)).
End Fol_Full.
Section Fol_Plus.
Definition ifThenElseH (A B C : Formula) := andH (impH A B) (impH (notH A) C).
End Fol_Plus.
Section Formula_Decideability.
Definition language_decideable := ((forall x y : Functions L, {x = y} + {x <> y}) * (forall x y : Relations L, {x = y} + {x <> y}))%type.
Hypothesis language_dec : language_decideable.
Let nilTermsHelp : forall n : nat, n = 0 -> Terms n.
intros.
induction n as [| n Hrecn].
apply Tnil.
discriminate H.
Defined.
Let consTermsHelp : forall n : nat, Terms n -> Set.
intros.
case n.
exact (forall p : 0 = n, {foo : unit | eq_rec _ (fun z => Terms z) Tnil _ p = H}).
intros.
exact (forall p : S n0 = n, {t : Term * Terms n0 | eq_rec _ (fun z => Terms z) (Tcons n0 (fst t) (snd t)) _ p = H}).
Defined.
End Formula_Decideability.
Section Formula_Depth_Induction.
Fixpoint depth (A : Formula) : nat := match A with | equal _ _ => 0 | atomic _ _ => 0 | impH A B => S (max (depth A) (depth B)) | notH A => S (depth A) | forallH _ A => S (depth A) end.
Definition lt_depth (A B : Formula) : Prop := depth A < depth B.
Definition Formula_depth_rec_rec : forall P : Formula -> Set, (forall a : Formula, (forall b : Formula, lt_depth b a -> P b) -> P a) -> forall (n : nat) (b : Formula), depth b <= n -> P b.
intros P H n.
induction n as [| n Hrecn].
intros.
apply H.
intros.
unfold lt_depth in H1.
rewrite <- (le_n_O_eq _ H0) in H1.
elim (lt_n_O _ H1).
intros.
apply H.
intros.
apply Hrecn.
apply lt_n_Sm_le.
apply lt_le_trans with (depth b).
apply H1.
apply H0.
Defined.
Definition Formula_depth_rec (P : Formula -> Set) (rec : forall a : Formula, (forall b : Formula, lt_depth b a -> P b) -> P a) (a : Formula) : P a := Formula_depth_rec_rec P rec (depth a) a (le_n (depth a)).
Definition Formula_depth_rec2rec (P : Formula -> Set) (f1 : forall t t0 : Term, P (equal t t0)) (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))), P (atomic r t)) (f3 : forall f : Formula, P f -> forall f0 : Formula, P f0 -> P (impH f f0)) (f4 : forall f : Formula, P f -> P (notH f)) (f5 : forall (v : nat) (a : Formula), (forall b : Formula, lt_depth b (forallH v a) -> P b) -> P (forallH v a)) (a : Formula) : (forall b : Formula, lt_depth b a -> P b) -> P a := match a return ((forall b : Formula, lt_depth b a -> P b) -> P a) with | equal t s => fun _ => f1 t s | atomic r t => fun _ => f2 r t | impH f g => fun hyp => f3 f (hyp f (depthImp1 f g)) g (hyp g (depthImp2 f g)) | notH f => fun hyp => f4 f (hyp f (depthNot f)) | forallH n f => fun hyp => f5 n f hyp end.
Definition Formula_depth_rec2 (P : Formula -> Set) (f1 : forall t t0 : Term, P (equal t t0)) (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))), P (atomic r t)) (f3 : forall f : Formula, P f -> forall f0 : Formula, P f0 -> P (impH f f0)) (f4 : forall f : Formula, P f -> P (notH f)) (f5 : forall (v : nat) (a : Formula), (forall b : Formula, lt_depth b (forallH v a) -> P b) -> P (forallH v a)) (a : Formula) : P a := Formula_depth_rec P (Formula_depth_rec2rec P f1 f2 f3 f4 f5) a.
Remark Formula_depth_rec2rec_nice : forall (Q P : Formula -> Set) (f1 : forall t t0 : Term, Q (equal t t0) -> P (equal t t0)) (f2 : forall (r : Relations L) (t : Terms (arity L (inl (Functions L) r))), Q (atomic r t) -> P (atomic r t)) (f3 : forall f : Formula, (Q f -> P f) -> forall f0 : Formula, (Q f0 -> P f0) -> Q (impH f f0) -> P (impH f f0)), (forall (f g : Formula) (z1 z2 : Q f -> P f), (forall q : Q f, z1 q = z2 q) -> forall z3 z4 : Q g -> P g, (forall q : Q g, z3 q = z4 q) -> forall q : Q (impH f g), f3 f z1 g z3 q = f3 f z2 g z4 q) -> forall f4 : forall f : Formula, (Q f -> P f) -> Q (notH f) -> P (notH f), (forall (f : Formula) (z1 z2 : Q f -> P f), (forall q : Q f, z1 q = z2 q) -> forall q : Q (notH f), f4 f z1 q = f4 f z2 q) -> forall f5 : forall (v : nat) (a : Formula), (forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b) -> Q (forallH v a) -> P (forallH v a), (forall (v : nat) (a : Formula) (z1 z2 : forall b : Formula, lt_depth b (forallH v a) -> Q b -> P b), (forall (b : Formula) (q : lt_depth b (forallH v a)) (r : Q b), z1 b q r = z2 b q r) -> forall q : Q (forallH v a), f5 v a z1 q = f5 v a z2 q) -> forall (a : Formula) (z1 z2 : forall b : Formula, lt_depth b a -> Q b -> P b), (forall (b : Formula) (p : lt_depth b a) (q : Q b), z1 b p q = z2 b p q) -> forall q : Q a, Formula_depth_rec2rec (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a z1 q = Formula_depth_rec2rec (fun x : Formula => Q x -> P x) f1 f2 f3 f4 f5 a z2 q.
Proof.
intros.
induction a as [t t0| r t| a1 Hreca1 a0 Hreca0| a Hreca| n a Hreca].
auto.
auto.
simpl in |- *.
apply H.
intros.
apply H2.
intros.
apply H2.
simpl in |- *.
apply H0.
intros.
apply H2.
simpl in |- *.
apply H1.
apply H2.
Definition Formula_depth_ind : forall P : Formula -> Prop, (forall a : Formula, (forall b : Formula, lt_depth b a -> P b) -> P a) -> forall a : Formula, P a.
Proof.
intros.
assert (forall (n : nat) (b : Formula), depth b <= n -> P b).
intro.
induction n as [| n Hrecn].
intros.
apply H.
intros.
unfold lt_depth in H1.
rewrite <- (le_n_O_eq _ H0) in H1.
elim (lt_n_O _ H1).
intros.
apply H.
intros.
apply Hrecn.
apply lt_n_Sm_le.
apply lt_le_trans with (depth b).
apply H1.
apply H0.
eapply H0.
apply le_n.
End Formula_Depth_Induction.
End First_Order_Logic.

Lemma Formula_depth_rec_indep : forall (Q P : Formula -> Set) (rec : forall a : Formula, (forall b : Formula, lt_depth b a -> Q b -> P b) -> Q a -> P a), (forall (a : Formula) (z1 z2 : forall b : Formula, lt_depth b a -> Q b -> P b), (forall (b : Formula) (p : lt_depth b a) (q : Q b), z1 b p q = z2 b p q) -> forall q : Q a, rec a z1 q = rec a z2 q) -> forall (a : Formula) (q : Q a), Formula_depth_rec (fun x : Formula => Q x -> P x) rec a q = rec a (fun (b : Formula) _ => Formula_depth_rec (fun x : Formula => Q x -> P x) rec b) q.
Proof.
intros Q P rec H.
unfold Formula_depth_rec in |- *.
set (H0 := Formula_depth_rec_rec (fun x : Formula => Q x -> P x) rec) in *.
assert (forall (n m : nat) (b : Formula) (l1 : depth b <= n) (l2 : depth b <= m) (q : Q b), H0 n b l1 q = H0 m b l2 q).
simple induction n.
simpl in |- *.
intros.
induction m as [| m Hrecm].
simpl in |- *.
apply H.
intros.
induction (lt_n_O (depth b0) (eq_ind_r (fun n0 : nat => depth b0 < n0) p (le_n_O_eq (depth b) l1))).
intros.
simpl in |- *.
apply H.
intros.
induction (lt_n_O (depth b0) (eq_ind_r (fun n0 : nat => depth b0 < n0) p (le_n_O_eq (depth b) l1))).
simple induction m.
intros.
simpl in |- *.
apply H.
intros.
induction (lt_n_O (depth b0) (eq_ind_r (fun n1 : nat => depth b0 < n1) p (le_n_O_eq (depth b) l2))).
intros.
simpl in |- *.
apply H.
intros.
apply H1.
intros.
replace (H0 (depth a) a (le_n (depth a)) q) with (H0 (S (depth a)) a (le_n_Sn (depth a)) q).
simpl in |- *.
apply H.
intros.
apply H1.
apply H1.

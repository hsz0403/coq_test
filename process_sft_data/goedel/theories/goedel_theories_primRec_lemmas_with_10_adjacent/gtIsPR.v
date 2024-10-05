Require Import Arith.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Coq.Lists.List.
Require Import Eqdep_dec.
Require Import extEqualNat.
Require Vector.
Require Import misc.
Require Export Bool.
Require Export EqNat.
Require Import Even.
Require Import Max.
Inductive PrimRec : nat -> Set := | succFunc : PrimRec 1 | zeroFunc : PrimRec 0 | projFunc : forall n m : nat, m < n -> PrimRec n | composeFunc : forall (n m : nat) (g : PrimRecs n m) (h : PrimRec m), PrimRec n | primRecFunc : forall (n : nat) (g : PrimRec n) (h : PrimRec (S (S n))), PrimRec (S n) with PrimRecs : nat -> nat -> Set := | PRnil : forall n : nat, PrimRecs n 0 | PRcons : forall n m : nat, PrimRec n -> PrimRecs n m -> PrimRecs n (S m).
Scheme PrimRec_PrimRecs_rec := Induction for PrimRec Sort Set with PrimRecs_PrimRec_rec := Induction for PrimRecs Sort Set.
Scheme PrimRec_PrimRecs_ind := Induction for PrimRec Sort Prop with PrimRecs_PrimRec_ind := Induction for PrimRecs Sort Prop.
Fixpoint evalConstFunc (n m : nat) {struct n} : naryFunc n := match n return (naryFunc n) with | O => m | S n' => fun _ => evalConstFunc n' m end.
Fixpoint evalProjFunc (n : nat) : forall m : nat, m < n -> naryFunc n := match n return (forall m : nat, m < n -> naryFunc n) with | O => fun (m : nat) (l : m < 0) => False_rec _ (lt_n_O _ l) | S n' => fun (m : nat) (l : m < S n') => match eq_nat_dec m n' with | left _ => fun a : nat => evalConstFunc _ a | right l1 => fun _ => evalProjFunc n' m match le_lt_or_eq _ _ (lt_n_Sm_le _ _ l) with | or_introl l2 => l2 | or_intror l2 => False_ind _ (l1 l2) end end end.
Fixpoint evalList (m : nat) (l : Vector.t nat m) {struct l} : naryFunc m -> nat := match l in (Vector.t _ m) return (naryFunc m -> nat) with | Vector.nil => fun x : naryFunc 0 => x | Vector.cons a n l' => fun x : naryFunc (S n) => evalList n l' (x a) end.
Fixpoint evalOneParamList (n m a : nat) (l : Vector.t (naryFunc (S n)) m) {struct l} : Vector.t (naryFunc n) m := match l in (Vector.t _ m) return (Vector.t (naryFunc n) m) with | Vector.nil => Vector.nil (naryFunc n) | Vector.cons f m' l' => Vector.cons _ (f a) m' (evalOneParamList n m' a l') end.
Fixpoint evalComposeFunc (n : nat) : forall m : nat, Vector.t (naryFunc n) m -> naryFunc m -> naryFunc n := match n return (forall m : nat, Vector.t (naryFunc n) m -> naryFunc m -> naryFunc n) with | O => evalList | S n' => fun (m : nat) (l : Vector.t (naryFunc (S n')) m) (f : naryFunc m) (a : nat) => evalComposeFunc n' m (evalOneParamList _ _ a l) f end.
Fixpoint compose2 (n : nat) : naryFunc n -> naryFunc (S n) -> naryFunc n := match n return (naryFunc n -> naryFunc (S n) -> naryFunc n) with | O => fun (a : nat) (g : nat -> nat) => g a | S n' => fun (f : naryFunc (S n')) (g : naryFunc (S (S n'))) (a : nat) => compose2 n' (f a) (fun x : nat => g x a) end.
Fixpoint evalPrimRecFunc (n : nat) (g : naryFunc n) (h : naryFunc (S (S n))) (a : nat) {struct a} : naryFunc n := match a with | O => g | S a' => compose2 _ (evalPrimRecFunc n g h a') (h a') end.
Fixpoint evalPrimRec (n : nat) (f : PrimRec n) {struct f} : naryFunc n := match f in (PrimRec n) return (naryFunc n) with | succFunc => S | zeroFunc => 0 | projFunc n m pf => evalProjFunc n m pf | composeFunc n m l f => evalComposeFunc n m (evalPrimRecs _ _ l) (evalPrimRec _ f) | primRecFunc n g h => evalPrimRecFunc n (evalPrimRec _ g) (evalPrimRec _ h) end with evalPrimRecs (n m : nat) (fs : PrimRecs n m) {struct fs} : Vector.t (naryFunc n) m := match fs in (PrimRecs n m) return (Vector.t (naryFunc n) m) with | PRnil a => Vector.nil (naryFunc a) | PRcons a b g gs => Vector.cons _ (evalPrimRec _ g) _ (evalPrimRecs _ _ gs) end.
Definition extEqualVectorGeneral (n m : nat) (l : Vector.t (naryFunc n) m) : forall (m' : nat) (l' : Vector.t (naryFunc n) m'), Prop.
induction l as [| a n0 l Hrecl].
intros.
destruct l' as [| a n0 v].
exact True.
exact False.
intros.
destruct l' as [| a0 n1 v].
exact False.
exact (extEqual n a a0 /\ Hrecl _ v).
Defined.
Definition extEqualVector n: forall m (l l' : Vector.t (naryFunc n) m), Prop.
refine (@Vector.rect2 _ _ _ _ _); intros.
apply True.
apply (extEqual n a b /\ X).
Defined.
Definition isPR (n : nat) (f : naryFunc n) : Set := {p : PrimRec n | extEqual n (evalPrimRec _ p) f}.
Definition isPRrel (n : nat) (R : naryRel n) : Set := isPR n (charFunction n R).
Definition notZero (a : nat) := nat_rec (fun n : nat => nat) 0 (fun x y : nat => 1) a.
Definition ltBool (a b : nat) : bool.
intros.
destruct (le_lt_dec b a).
exact false.
exact true.
Defined.
Remark replaceCompose2 : forall (n : nat) (a b a' b' : naryFunc n) (c c' : naryFunc 2), extEqual n a a' -> extEqual n b b' -> extEqual 2 c c' -> extEqual n (evalComposeFunc _ _ (Vector.cons _ a _ (Vector.cons _ b _ (Vector.nil (naryFunc n)))) c) (evalComposeFunc _ _ (Vector.cons _ a' _ (Vector.cons _ b' _ (Vector.nil (naryFunc n)))) c').
Proof.
intros.
apply extEqualCompose.
unfold extEqualVector in |- *.
simpl in |- *.
auto.
auto.
Definition orRel (n : nat) (R S : naryRel n) : naryRel n.
intros.
induction n as [| n Hrecn].
apply (R || S).
simpl in |- *.
intros.
apply Hrecn.
apply (R H).
apply (S H).
Defined.
Definition andRel (n : nat) (R S : naryRel n) : naryRel n.
intros.
induction n as [| n Hrecn].
exact (R && S).
simpl in |- *.
intros.
apply Hrecn.
apply (R H).
apply (S H).
Defined.
Definition notRel (n : nat) (R : naryRel n) : naryRel n.
intros.
induction n as [| n Hrecn].
exact (negb R).
simpl in |- *.
intros.
apply Hrecn.
apply (R H).
Defined.
Fixpoint bodd (n : nat) : bool := match n with | O => false | S n' => negb (bodd n') end.
Definition leBool (a b : nat) : bool.
intros.
destruct (le_lt_dec a b).
exact true.
exact false.
Defined.
Section Ignore_Params.
Fixpoint ignoreParams (n m : nat) (f : naryFunc n) {struct m} : naryFunc (m + n) := match m return (naryFunc (m + n)) with | O => f | S x => fun _ => ignoreParams n x f end.
Definition projectionListPR (n m : nat) (p : m <= n) : PrimRecs n m.
intros.
induction m as [| m Hrecm].
exact (PRnil n).
assert (m < n).
apply lt_S_n.
apply le_lt_n_Sm.
apply p.
apply (PRcons _ m (projFunc _ _ H)).
apply Hrecm.
apply le_S_n.
apply le_S.
apply p.
Defined.
Definition projectionList (n m : nat) (p : m <= n) : Vector.t (naryFunc n) m := evalPrimRecs n m (projectionListPR n m p).
End Ignore_Params.
Definition switchPR : naryFunc 3.
simpl in |- *.
intros.
destruct H as [| n].
apply H1.
apply H0.
Defined.
Fixpoint boundedSearchHelp (P : naryRel 1) (b : nat) {struct b} : nat := match b with | O => 0 | S b' => match eq_nat_dec (boundedSearchHelp P b') b' with | left _ => match P b' with | true => b' | false => S b' end | right _ => boundedSearchHelp P b' end end.
Definition boundedSearch (P : naryRel 2) (b : nat) : nat := boundedSearchHelp (P b) b.
Definition iterate (g : nat -> nat) := nat_rec (fun _ => nat -> nat) (fun x : nat => x) (fun (_ : nat) (rec : nat -> nat) (x : nat) => g (rec x)).

Lemma multIsPR : isPR 2 mult.
Proof.
assert (isPR 2 (fun a b : nat => nat_rec (fun n : nat => nat) 0 (fun x y : nat => y + b) a)).
assert (isPR 1 (fun _ => 0)).
apply const1_NIsPR.
apply (ind1ParamIsPR _ multIndIsPR _ H).
induction H as (x, p).
simpl in p.
exists x.
simpl in |- *.
intros.
rewrite p.
induction c as [| c Hrecc].
auto.
simpl in |- *.
rewrite Hrecc.
Admitted.

Lemma predIsPR : isPR 1 pred.
Proof.
assert (isPR 1 (fun a : nat => nat_rec (fun n : nat => nat) 0 (fun x y : nat => x) a)).
apply (indIsPR _ pi1_2IsPR 0).
induction H as (x, p).
simpl in p.
exists x.
simpl in |- *.
intros.
rewrite p.
induction c as [| c Hrecc].
auto.
Admitted.

Lemma minusIndIsPR : isPR 3 (fun n fn b : nat => pred fn).
Admitted.

Lemma minusIsPR : isPR 2 minus.
Proof.
assert (isPR 2 (fun b a : nat => nat_rec (fun n : nat => nat) b (fun x y : nat => pred y) a)).
apply swapIsPR with (f := fun a b : nat => nat_rec (fun n : nat => nat) b (fun x y : nat => pred y) a).
apply (ind1ParamIsPR _ minusIndIsPR _ idIsPR).
induction H as (x, p).
simpl in p.
exists x.
simpl in |- *.
intros.
rewrite p.
induction c0 as [| c0 Hrecc0].
simpl in |- *.
apply minus_n_O.
simpl in |- *.
rewrite Hrecc0.
generalize c c0.
intro.
induction c1 as [| c1 Hrecc1].
intros.
auto.
intros.
simpl in |- *.
induction c2 as [| c2 Hrecc2].
simpl in |- *.
apply minus_n_O.
Admitted.

Lemma notZeroIsPR : isPR 1 notZero.
Proof.
unfold notZero in |- *.
apply indIsPR with (f := fun _ _ : nat => 1).
apply filter10IsPR with (g := fun _ : nat => 1).
Admitted.

Definition ltBool (a b : nat) : bool.
intros.
destruct (le_lt_dec b a).
exact false.
Admitted.

Lemma ltBoolTrue : forall a b : nat, ltBool a b = true -> a < b.
intros.
unfold ltBool in H.
induction (le_lt_dec b a).
discriminate H.
Admitted.

Lemma ltBoolFalse : forall a b : nat, ltBool a b = false -> ~ a < b.
intros.
unfold ltBool in H.
induction (le_lt_dec b a).
unfold not in |- *; intros.
elim (le_not_lt _ _ a0).
auto.
Admitted.

Lemma ltIsPR : isPRrel 2 ltBool.
Proof.
unfold isPRrel in |- *.
assert (isPR 2 (fun a b : nat => notZero (b - a))).
apply swapIsPR with (f := fun a b : nat => notZero (a - b)).
apply compose2_1IsPR.
apply minusIsPR.
apply notZeroIsPR.
induction H as (x, p).
simpl in p.
exists x.
simpl in |- *.
intros.
rewrite p.
unfold ltBool in |- *.
induction (le_lt_dec c0 c).
cut (c0 <= c).
generalize c.
clear c a.
induction c0 as [| c0 Hrecc0].
intros.
reflexivity.
intros.
induction c as [| c Hrecc].
elim (le_Sn_O _ H).
simpl in |- *.
apply Hrecc0.
apply le_S_n.
auto.
auto.
cut (c < c0).
generalize c.
clear c b.
induction c0 as [| c0 Hrecc0].
intros.
elim (lt_n_O _ H).
intros.
induction c as [| c Hrecc].
simpl in |- *.
reflexivity.
simpl in |- *.
apply Hrecc0.
apply lt_S_n.
auto.
Admitted.

Lemma maxIsPR : isPR 2 max.
Proof.
assert (isPR 2 (fun a b : nat => a + (b - a))).
apply compose2_2IsPR with (h := plus) (f := fun a b : nat => a) (g := fun a b : nat => b - a).
apply pi1_2IsPR.
apply swapIsPR.
apply minusIsPR.
apply plusIsPR.
induction H as (x, p).
exists x.
eapply extEqualTrans.
apply p.
clear x p.
simpl in |- *.
intros.
induction (le_or_lt c c0).
rewrite max_r.
symmetry in |- *.
apply le_plus_minus.
assumption.
assumption.
rewrite not_le_minus_0.
rewrite plus_comm.
rewrite max_l.
reflexivity.
apply lt_le_weak.
assumption.
apply lt_not_le.
Admitted.

Remark replaceCompose2 : forall (n : nat) (a b a' b' : naryFunc n) (c c' : naryFunc 2), extEqual n a a' -> extEqual n b b' -> extEqual 2 c c' -> extEqual n (evalComposeFunc _ _ (Vector.cons _ a _ (Vector.cons _ b _ (Vector.nil (naryFunc n)))) c) (evalComposeFunc _ _ (Vector.cons _ a' _ (Vector.cons _ b' _ (Vector.nil (naryFunc n)))) c').
Proof.
intros.
apply extEqualCompose.
unfold extEqualVector in |- *.
simpl in |- *.
auto.
Admitted.

Definition orRel (n : nat) (R S : naryRel n) : naryRel n.
intros.
induction n as [| n Hrecn].
apply (R || S).
simpl in |- *.
intros.
apply Hrecn.
apply (R H).
Admitted.

Lemma orRelPR : forall (n : nat) (R R' : naryRel n), isPRrel n R -> isPRrel n R' -> isPRrel n (orRel n R R').
Proof.
intros.
induction H as (x, p).
induction H0 as (x0, p0).
assert (isPR 2 (fun a b : nat => notZero (a + b))).
apply compose2_1IsPR.
apply plusIsPR.
apply notZeroIsPR.
induction H as (x1, p1).
exists (composeFunc _ _ (PRcons _ _ x (PRcons _ _ x0 (PRnil _))) x1).
simpl in |- *.
apply extEqualTrans with (evalComposeFunc n 2 (Vector.cons (naryFunc n) (charFunction n R) 1 (Vector.cons (naryFunc n) (charFunction n R') 0 (Vector.nil (naryFunc n)))) (fun a b : nat => notZero (a + b))).
apply replaceCompose2; auto.
clear x p x0 p0 x1 p1.
induction n as [| n Hrecn].
simpl in |- *.
induction R.
reflexivity.
induction R'.
reflexivity.
reflexivity.
simpl in |- *.
fold (naryFunc n) in |- *.
intros.
Admitted.

Definition andRel (n : nat) (R S : naryRel n) : naryRel n.
intros.
induction n as [| n Hrecn].
exact (R && S).
simpl in |- *.
intros.
apply Hrecn.
apply (R H).
Admitted.

Lemma andRelPR : forall (n : nat) (R R' : naryRel n), isPRrel n R -> isPRrel n R' -> isPRrel n (andRel n R R').
Proof.
intros.
induction H as (x, p).
induction H0 as (x0, p0).
assert (isPR 2 mult).
apply multIsPR.
induction H as (x1, p1).
exists (composeFunc _ _ (PRcons _ _ x (PRcons _ _ x0 (PRnil _))) x1).
simpl in |- *.
apply extEqualTrans with (evalComposeFunc n 2 (Vector.cons (naryFunc n) (charFunction n R) 1 (Vector.cons (naryFunc n) (charFunction n R') 0 (Vector.nil (naryFunc n)))) mult).
apply replaceCompose2; auto.
clear x p x0 p0 x1 p1.
induction n as [| n Hrecn].
simpl in |- *.
induction R.
induction R'.
reflexivity.
reflexivity.
reflexivity.
simpl in |- *.
fold (naryFunc n) in |- *.
intros.
Admitted.

Definition notRel (n : nat) (R : naryRel n) : naryRel n.
intros.
induction n as [| n Hrecn].
exact (negb R).
simpl in |- *.
intros.
apply Hrecn.
Admitted.

Lemma notRelPR : forall (n : nat) (R : naryRel n), isPRrel n R -> isPRrel n (notRel n R).
Proof.
intros.
induction H as (x, p).
assert (isPR 1 (fun x : nat => 1 - x)).
apply compose1_2IsPR with (f := fun x : nat => 1) (f' := fun x : nat => x).
apply const1_NIsPR.
apply idIsPR.
apply minusIsPR.
induction H as (x0, p0).
exists (composeFunc _ _ (PRcons _ _ x (PRnil _)) x0).
simpl in |- *.
apply extEqualTrans with (evalComposeFunc n 1 (Vector.cons _ (charFunction n R) _ (Vector.nil _)) (fun x : nat => 1 - x)).
apply extEqualCompose.
unfold extEqualVector in |- *.
simpl in |- *.
auto.
auto.
clear p0 x0 p x.
induction n as [| n Hrecn].
simpl in |- *.
induction R.
reflexivity.
reflexivity.
simpl in |- *.
intros.
fold (naryFunc n) in |- *.
Admitted.

Lemma boddIsPR : isPRrel 1 bodd.
Proof.
assert (isPR 2 (fun _ rec : nat => 1 - rec)).
apply filter01IsPR with (g := fun rec : nat => 1 - rec).
apply compose1_2IsPR with (f := fun _ : nat => 1) (f' := fun x : nat => x).
apply const1_NIsPR.
apply idIsPR.
apply minusIsPR.
induction H as (x, p).
exists (primRecFunc 0 zeroFunc x).
simpl in |- *.
intros.
induction c as [| c Hrecc].
simpl in |- *.
auto.
simpl in |- *.
rewrite p.
simpl in |- *.
rewrite Hrecc.
clear Hrecc.
induction (bodd c).
reflexivity.
Admitted.

Lemma beq_nat_not_refl : forall a b : nat, a <> b -> beq_nat a b = false.
Proof.
double induction a b.
intros.
elim H.
auto.
auto.
auto.
intros.
simpl in |- *.
Admitted.

Lemma neqIsPR : isPRrel 2 (fun a b : nat => negb (beq_nat a b)).
Proof.
intros.
assert (isPRrel 2 (orRel 2 ltBool (fun a b : nat => ltBool b a))).
apply orRelPR.
apply ltIsPR.
apply gtIsPR.
induction H as (x, p).
exists x.
simpl in |- *.
simpl in p.
intros.
rewrite p.
clear p.
unfold ltBool in |- *.
induction (eq_nat_dec c c0).
rewrite a.
rewrite <- beq_nat_refl.
simpl in |- *.
induction (le_lt_dec c0 c0).
simpl in |- *.
reflexivity.
elim (lt_irrefl _ b).
rewrite beq_nat_not_refl.
simpl in |- *.
induction (le_lt_dec c0 c).
induction (le_lt_dec c c0).
induction (nat_total_order _ _ b).
elim (lt_not_le _ _ H).
auto.
elim (lt_not_le _ _ H).
auto.
reflexivity.
reflexivity.
Admitted.

Lemma gtIsPR : isPRrel 2 (fun a b : nat => ltBool b a).
Proof.
intros.
unfold isPRrel in |- *.
simpl in |- *.
apply swapIsPR with (f := fun a0 a : nat => if ltBool a0 a then 1 else 0).
apply ltIsPR.

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

Lemma compose3_1IsPR : forall f : nat -> nat -> nat -> nat, isPR 3 f -> forall g : nat -> nat, isPR 1 g -> isPR 3 (fun x y z : nat => g (f x y z)).
Proof.
intros.
induction H as (x, p); simpl in p.
induction H0 as (x0, p0); simpl in p0.
exists (composeFunc _ _ (PRcons _ _ x (PRnil _)) x0).
simpl in |- *.
intros.
rewrite <- p.
rewrite <- p0.
Admitted.

Lemma compose3_2IsPR : forall f1 : nat -> nat -> nat -> nat, isPR 3 f1 -> forall f2 : nat -> nat -> nat -> nat, isPR 3 f2 -> forall g : nat -> nat -> nat, isPR 2 g -> isPR 3 (fun x y z : nat => g (f1 x y z) (f2 x y z)).
Proof.
intros.
induction H as (x, p); simpl in p.
induction H0 as (x0, p0); simpl in p0.
induction H1 as (x1, p1); simpl in p1.
exists (composeFunc _ _ (PRcons _ _ x (PRcons _ _ x0 (PRnil _))) x1).
simpl in |- *.
intros.
rewrite <- p.
rewrite <- p0.
rewrite <- p1.
Admitted.

Lemma compose3_3IsPR : forall f1 : nat -> nat -> nat -> nat, isPR 3 f1 -> forall f2 : nat -> nat -> nat -> nat, isPR 3 f2 -> forall f3 : nat -> nat -> nat -> nat, isPR 3 f3 -> forall g : nat -> nat -> nat -> nat, isPR 3 g -> isPR 3 (fun x y z : nat => g (f1 x y z) (f2 x y z) (f3 x y z)).
Proof.
intros.
induction H as (x, p); simpl in p.
induction H0 as (x0, p0); simpl in p0.
induction H1 as (x1, p1); simpl in p1.
induction H2 as (x2, p2); simpl in p2.
exists (composeFunc _ _ (PRcons _ _ x (PRcons _ _ x0 (PRcons _ _ x1 (PRnil _)))) x2).
simpl in |- *.
intros.
rewrite <- p.
rewrite <- p0.
rewrite <- p1.
rewrite <- p2.
Admitted.

Lemma compose4_2IsPR : forall f1 : nat -> nat -> nat -> nat -> nat, isPR 4 f1 -> forall f2 : nat -> nat -> nat -> nat -> nat, isPR 4 f2 -> forall g : nat -> nat -> nat, isPR 2 g -> isPR 4 (fun w x y z : nat => g (f1 w x y z) (f2 w x y z)).
Proof.
intros.
induction H as (x, p); simpl in p.
induction H0 as (x0, p0); simpl in p0.
induction H1 as (x1, p1); simpl in p1.
exists (composeFunc _ _ (PRcons _ _ x (PRcons _ _ x0 (PRnil _))) x1).
simpl in |- *.
intros.
rewrite <- p.
rewrite <- p0.
rewrite <- p1.
Admitted.

Lemma compose4_3IsPR : forall f1 : nat -> nat -> nat -> nat -> nat, isPR 4 f1 -> forall f2 : nat -> nat -> nat -> nat -> nat, isPR 4 f2 -> forall f3 : nat -> nat -> nat -> nat -> nat, isPR 4 f3 -> forall g : nat -> nat -> nat -> nat, isPR 3 g -> isPR 4 (fun w x y z : nat => g (f1 w x y z) (f2 w x y z) (f3 w x y z)).
Proof.
intros.
induction H as (x, p); simpl in p.
induction H0 as (x0, p0); simpl in p0.
induction H1 as (x1, p1); simpl in p1.
induction H2 as (x2, p2); simpl in p2.
exists (composeFunc _ _ (PRcons _ _ x (PRcons _ _ x0 (PRcons _ _ x1 (PRnil _)))) x2).
simpl in |- *.
intros.
rewrite <- p.
rewrite <- p0.
rewrite <- p1.
rewrite <- p2.
Admitted.

Lemma swapIsPR : forall f : nat -> nat -> nat, isPR 2 f -> isPR 2 (fun x y : nat => f y x).
Proof.
intros.
apply compose2_2IsPR with (f := fun a b : nat => b) (g := fun a b : nat => a).
apply pi2_2IsPR.
apply pi1_2IsPR.
Admitted.

Lemma indIsPR : forall f : nat -> nat -> nat, isPR 2 f -> forall g : nat, isPR 1 (fun a : nat => nat_rec (fun n : nat => nat) g (fun x y : nat => f x y) a).
Proof.
intros.
induction H as (x, p).
simpl in p.
induction (const0_NIsPR g).
simpl in p0.
exists (primRecFunc _ x0 x).
simpl in |- *.
simple induction c.
simpl in |- *.
rewrite <- p0.
auto.
intros.
simpl in |- *.
rewrite <- p.
rewrite <- H.
Admitted.

Lemma ind1ParamIsPR : forall f : nat -> nat -> nat -> nat, isPR 3 f -> forall g : nat -> nat, isPR 1 g -> isPR 2 (fun a b : nat => nat_rec (fun n : nat => nat) (g b) (fun x y : nat => f x y b) a).
Proof.
intros.
induction H as (x, p).
simpl in p.
induction H0 as (x0, p0).
simpl in p0.
exists (primRecFunc _ x0 x).
simpl in |- *.
intros.
induction c as [| c Hrecc].
simpl in |- *.
apply p0.
simpl in |- *.
rewrite p.
rewrite Hrecc.
Admitted.

Lemma ind2ParamIsPR : forall f : nat -> nat -> nat -> nat -> nat, isPR 4 f -> forall g : nat -> nat -> nat, isPR 2 g -> isPR 3 (fun a b c : nat => nat_rec (fun n : nat => nat) (g b c) (fun x y : nat => f x y b c) a).
Proof.
intros.
induction H as (x, p).
simpl in p.
induction H0 as (x0, p0).
simpl in p0.
exists (primRecFunc _ x0 x).
simpl in |- *.
simple induction c.
intros.
simpl in |- *.
rewrite p0.
auto.
intros.
simpl in |- *.
rewrite p.
rewrite H.
Admitted.

Lemma plusIndIsPR : isPR 3 (fun n fn b : nat => S fn).
Admitted.

Lemma multIndIsPR : isPR 3 (fun n fn b : nat => fn + b).
Admitted.

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

Lemma plusIsPR : isPR 2 plus.
Proof.
assert (isPR 2 (fun a b : nat => nat_rec (fun n : nat => nat) b (fun x y : nat => S y) a)).
apply (ind1ParamIsPR _ plusIndIsPR _ idIsPR).
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
auto.

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

Definition extEqualVector n: forall m (l l' : Vector.t (naryFunc n) m), Prop.
refine (@Vector.rect2 _ _ _ _ _); intros.
apply True.
Admitted.

Lemma extEqualVectorRefl : forall (n m : nat) (l : Vector.t (naryFunc n) m), extEqualVector n m l l.
Proof.
intros.
induction l as [| a n0 l Hrecl].
now simpl.
split.
apply extEqualRefl.
Admitted.

Lemma extEqualOneParamList : forall (n m : nat) (l1 l2 : Vector.t (naryFunc (S n)) m) (c : nat), extEqualVector (S n) m l1 l2 -> extEqualVector n m (evalOneParamList n m c l1) (evalOneParamList n m c l2).
Proof.
intro; refine (@Vector.rect2 _ _ _ _ _); simpl; intros.
auto.
destruct H0.
Admitted.

Lemma extEqualCompose : forall (n m : nat) (l1 l2 : Vector.t (naryFunc n) m) (f1 f2 : naryFunc m), extEqualVector n m l1 l2 -> extEqual m f1 f2 -> extEqual n (evalComposeFunc n m l1 f1) (evalComposeFunc n m l2 f2).
Proof.
induction n; refine (@Vector.rect2 _ _ _ _ _); simpl; intros.
assumption.
destruct H0; now (apply H; [|subst a]).
rewrite H0.
apply extEqualRefl.
destruct H0 as (Hi, Hj).
apply IHn.
split.
apply Hi.
now apply extEqualOneParamList.
Admitted.

Lemma extEqualCompose2 : forall (n : nat) (f1 f2 : naryFunc n), extEqual n f1 f2 -> forall g1 g2 : naryFunc (S n), extEqual (S n) g1 g2 -> extEqual n (compose2 n f1 g1) (compose2 n f2 g2).
Proof.
intro.
induction n as [| n Hrecn]; simpl in |- *; intros.
rewrite H.
apply H0.
Admitted.

Lemma extEqualPrimRec : forall (n : nat) (g1 g2 : naryFunc n) (h1 h2 : naryFunc (S (S n))), extEqual n g1 g2 -> extEqual (S (S n)) h1 h2 -> extEqual (S n) (evalPrimRecFunc n g1 h1) (evalPrimRecFunc n g2 h2).
Proof.
intros.
simpl in |- *.
intros.
induction c as [| c Hrecc].
simpl in |- *.
auto.
simpl in |- *.
cut (extEqual n (evalPrimRecFunc n g1 h1 c) (evalPrimRecFunc n g2 h2 c)).
cut (extEqual (S n) (h1 c) (h2 c)).
generalize (h1 c) (h2 c) (evalPrimRecFunc n g1 h1 c) (evalPrimRecFunc n g2 h2 c).
fold (naryFunc (S n)) in |- *.
clear Hrecc H0 h1 h2 g1 g2 H.
induction n as [| n Hrecn].
simpl in |- *.
intros.
rewrite H0.
apply H.
simpl in |- *.
intros.
apply Hrecn.
simpl in |- *.
intros.
apply H.
apply H0.
simpl in |- *.
intros.
simpl in H0.
apply H0.
Admitted.

Lemma succIsPR : isPR 1 S.
Proof.
exists succFunc.
simpl in |- *.
Admitted.

Lemma const0_NIsPR : forall n : nat, isPR 0 n.
Proof.
simple induction n.
exists zeroFunc.
simpl in |- *.
reflexivity.
intros.
induction H as (x, p).
exists (composeFunc _ _ (PRcons _ _ x (PRnil _)) succFunc).
simpl in |- *.
simpl in p.
rewrite p.
Admitted.

Lemma const1_NIsPR : forall n : nat, isPR 1 (fun _ => n).
Proof.
intros.
assert (isPR 0 n).
apply const0_NIsPR.
induction H as (x, p).
exists (composeFunc 1 _ (PRnil _) x).
simpl in |- *.
simpl in p.
Admitted.

Lemma idIsPR : isPR 1 (fun x : nat => x).
Proof.
assert (0 < 1).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi1_2IsPR : isPR 2 (fun a b : nat => a).
Proof.
assert (1 < 2).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi2_2IsPR : isPR 2 (fun a b : nat => b).
Proof.
assert (0 < 2).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi1_3IsPR : isPR 3 (fun a b c : nat => a).
Proof.
assert (2 < 3).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi2_3IsPR : isPR 3 (fun a b c : nat => b).
Proof.
assert (1 < 3).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi3_3IsPR : isPR 3 (fun a b c : nat => c).
Proof.
assert (0 < 3).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi1_4IsPR : isPR 4 (fun a b c d : nat => a).
Proof.
assert (3 < 4).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi2_4IsPR : isPR 4 (fun a b c d : nat => b).
Proof.
assert (2 < 4).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi3_4IsPR : isPR 4 (fun a b c d : nat => c).
Proof.
assert (1 < 4).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma pi4_4IsPR : isPR 4 (fun a b c d : nat => d).
Proof.
assert (0 < 4).
auto.
exists (projFunc _ _ H).
simpl in |- *.
Admitted.

Lemma filter01IsPR : forall g : nat -> nat, isPR 1 g -> isPR 2 (fun a b : nat => g b).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 2 (fun a b : nat => b)).
apply pi2_2IsPR.
induction H as (x0, p0).
simpl in p0.
exists (composeFunc _ _ (PRcons _ _ x0 (PRnil _)) x).
simpl in |- *.
intros.
replace (g c0) with (g (evalPrimRec 2 x0 c c0)).
rewrite <- p.
auto.
rewrite p0.
Admitted.

Lemma filter100IsPR : forall g : nat -> nat, isPR 1 g -> isPR 3 (fun a b c : nat => g a).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 3 (fun a b c : nat => a)).
apply pi1_3IsPR.
induction H as (x0, p0).
simpl in p0.
exists (composeFunc _ _ (PRcons _ _ x0 (PRnil _)) x).
simpl in |- *.
intros.
replace (g c) with (g (evalPrimRec 3 x0 c c0 c1)).
rewrite <- p.
auto.
rewrite p0.
Admitted.

Lemma filter010IsPR : forall g : nat -> nat, isPR 1 g -> isPR 3 (fun a b c : nat => g b).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 3 (fun a b c : nat => b)).
apply pi2_3IsPR.
induction H as (x0, p0).
simpl in p0.
exists (composeFunc _ _ (PRcons _ _ x0 (PRnil _)) x).
simpl in |- *.
intros.
replace (g c0) with (g (evalPrimRec 3 x0 c c0 c1)).
rewrite <- p.
auto.
rewrite p0.
Admitted.

Lemma filter001IsPR : forall g : nat -> nat, isPR 1 g -> isPR 3 (fun a b c : nat => g c).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 3 (fun a b c : nat => c)).
apply pi3_3IsPR.
induction H as (x0, p0).
simpl in p0.
exists (composeFunc _ _ (PRcons _ _ x0 (PRnil _)) x).
simpl in |- *.
intros.
replace (g c1) with (g (evalPrimRec 3 x0 c c0 c1)).
rewrite <- p.
auto.
rewrite p0.
Admitted.

Lemma filter011IsPR : forall g : nat -> nat -> nat, isPR 2 g -> isPR 3 (fun a b c : nat => g b c).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 3 (fun a b c : nat => b)).
apply pi2_3IsPR.
induction H as (x0, p0).
simpl in p0.
assert (isPR 3 (fun a b c : nat => c)).
apply pi3_3IsPR.
induction H as (x1, p1).
simpl in p1.
exists (composeFunc _ _ (PRcons _ _ x0 (PRcons _ _ x1 (PRnil _))) x).
simpl in |- *.
intros.
replace (g c0 c1) with (g (evalPrimRec 3 x0 c c0 c1) (evalPrimRec 3 x1 c c0 c1)).
rewrite <- p.
auto.
rewrite p0.
rewrite p1.
Admitted.

Lemma filter110IsPR : forall g : nat -> nat -> nat, isPR 2 g -> isPR 3 (fun a b c : nat => g a b).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 3 (fun a b c : nat => a)).
apply pi1_3IsPR.
induction H as (x0, p0).
simpl in p0.
assert (isPR 3 (fun a b c : nat => b)).
apply pi2_3IsPR.
induction H as (x1, p1).
simpl in p1.
exists (composeFunc _ _ (PRcons _ _ x0 (PRcons _ _ x1 (PRnil _))) x).
simpl in |- *.
intros.
replace (g c c0) with (g (evalPrimRec 3 x0 c c0 c1) (evalPrimRec 3 x1 c c0 c1)).
rewrite <- p.
auto.
rewrite p0.
rewrite p1.
Admitted.

Lemma filter101IsPR : forall g : nat -> nat -> nat, isPR 2 g -> isPR 3 (fun a b c : nat => g a c).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 3 (fun a b c : nat => a)).
apply pi1_3IsPR.
induction H as (x0, p0).
simpl in p0.
assert (isPR 3 (fun a b c : nat => c)).
apply pi3_3IsPR.
induction H as (x1, p1).
simpl in p1.
exists (composeFunc _ _ (PRcons _ _ x0 (PRcons _ _ x1 (PRnil _))) x).
simpl in |- *.
intros.
replace (g c c1) with (g (evalPrimRec 3 x0 c c0 c1) (evalPrimRec 3 x1 c c0 c1)).
rewrite <- p.
auto.
rewrite p0.
rewrite p1.
Admitted.

Lemma filter0011IsPR : forall g : nat -> nat -> nat, isPR 2 g -> isPR 4 (fun a b c d : nat => g c d).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 4 (fun a b c d : nat => c)).
apply pi3_4IsPR.
induction H as (x0, p0).
simpl in p0.
assert (isPR 4 (fun a b c d : nat => d)).
apply pi4_4IsPR.
induction H as (x1, p1).
simpl in p1.
exists (composeFunc _ _ (PRcons _ _ x0 (PRcons _ _ x1 (PRnil _))) x).
simpl in |- *.
intros.
replace (g c1 c2) with (g (evalPrimRec 4 x0 c c0 c1 c2) (evalPrimRec 4 x1 c c0 c1 c2)).
rewrite <- p.
auto.
rewrite p0.
rewrite p1.
Admitted.

Lemma filter1000IsPR : forall g : nat -> nat, isPR 1 g -> isPR 4 (fun a b c d : nat => g a).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 4 (fun a b c d : nat => a)).
apply pi1_4IsPR.
induction H as (x0, p0).
simpl in p0.
exists (composeFunc _ _ (PRcons _ _ x0 (PRnil _)) x).
simpl in |- *.
intros.
replace (g c) with (g (evalPrimRec 4 x0 c c0 c1 c2)).
rewrite <- p.
auto.
rewrite p0.
Admitted.

Lemma filter1011IsPR : forall g : nat -> nat -> nat -> nat, isPR 3 g -> isPR 4 (fun a b c d : nat => g a c d).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 4 (fun a b c d : nat => a)).
apply pi1_4IsPR.
assert (isPR 4 (fun a b c d : nat => c)).
apply pi3_4IsPR.
assert (isPR 4 (fun a b c d : nat => d)).
apply pi4_4IsPR.
induction H as (x0, p0).
simpl in p0.
induction H0 as (x1, p1).
simpl in p1.
induction H1 as (x2, p2).
simpl in p2.
exists (composeFunc _ _ (PRcons _ _ x0 (PRcons _ _ x1 (PRcons _ _ x2 (PRnil _)))) x).
simpl in |- *.
intros.
replace (g c c1 c2) with (g (evalPrimRec 4 x0 c c0 c1 c2) (evalPrimRec 4 x1 c c0 c1 c2) (evalPrimRec 4 x2 c c0 c1 c2)).
rewrite <- p.
auto.
rewrite p0.
Admitted.

Lemma filter1100IsPR : forall g : nat -> nat -> nat, isPR 2 g -> isPR 4 (fun a b c d : nat => g a b).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 4 (fun a b c d : nat => a)).
apply pi1_4IsPR.
assert (isPR 4 (fun a b c d : nat => b)).
apply pi2_4IsPR.
induction H as (x0, p0).
simpl in p0.
induction H0 as (x1, p1).
simpl in p1.
exists (composeFunc _ _ (PRcons _ _ x0 (PRcons _ _ x1 (PRnil _))) x).
simpl in |- *.
intros.
replace (g c c0) with (g (evalPrimRec 4 x0 c c0 c1 c2) (evalPrimRec 4 x1 c c0 c1 c2)).
rewrite <- p.
auto.
Admitted.

Lemma compose1_1IsPR : forall f : nat -> nat, isPR 1 f -> forall g : nat -> nat, isPR 1 g -> isPR 1 (fun x : nat => g (f x)).
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

Lemma compose1_2IsPR : forall f : nat -> nat, isPR 1 f -> forall f' : nat -> nat, isPR 1 f' -> forall g : nat -> nat -> nat, isPR 2 g -> isPR 1 (fun x : nat => g (f x) (f' x)).
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

Lemma compose1_3IsPR : forall f1 : nat -> nat, isPR 1 f1 -> forall f2 : nat -> nat, isPR 1 f2 -> forall f3 : nat -> nat, isPR 1 f3 -> forall g : nat -> nat -> nat -> nat, isPR 3 g -> isPR 1 (fun x : nat => g (f1 x) (f2 x) (f3 x)).
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

Lemma compose2_1IsPR : forall f : nat -> nat -> nat, isPR 2 f -> forall g : nat -> nat, isPR 1 g -> isPR 2 (fun x y : nat => g (f x y)).
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

Lemma compose2_2IsPR : forall f : nat -> nat -> nat, isPR 2 f -> forall g : nat -> nat -> nat, isPR 2 g -> forall h : nat -> nat -> nat, isPR 2 h -> isPR 2 (fun x y : nat => h (f x y) (g x y)).
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

Lemma compose2_3IsPR : forall f1 : nat -> nat -> nat, isPR 2 f1 -> forall f2 : nat -> nat -> nat, isPR 2 f2 -> forall f3 : nat -> nat -> nat, isPR 2 f3 -> forall g : nat -> nat -> nat -> nat, isPR 3 g -> isPR 2 (fun x y : nat => g (f1 x y) (f2 x y) (f3 x y)).
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

Lemma compose2_4IsPR : forall f1 : nat -> nat -> nat, isPR 2 f1 -> forall f2 : nat -> nat -> nat, isPR 2 f2 -> forall f3 : nat -> nat -> nat, isPR 2 f3 -> forall f4 : nat -> nat -> nat, isPR 2 f4 -> forall g : nat -> nat -> nat -> nat -> nat, isPR 4 g -> isPR 2 (fun x y : nat => g (f1 x y) (f2 x y) (f3 x y) (f4 x y)).
Proof.
intros.
induction H as (x, p); simpl in p.
induction H0 as (x0, p0); simpl in p0.
induction H1 as (x1, p1); simpl in p1.
induction H2 as (x2, p2); simpl in p2.
induction H3 as (x3, p3); simpl in p3.
exists (composeFunc _ _ (PRcons _ _ x (PRcons _ _ x0 (PRcons _ _ x1 (PRcons _ _ x2 (PRnil _))))) x3).
simpl in |- *.
intros.
rewrite <- p.
rewrite <- p0.
rewrite <- p1.
rewrite <- p2.
rewrite <- p3.
Admitted.

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

Lemma filter10IsPR : forall g : nat -> nat, isPR 1 g -> isPR 2 (fun a b : nat => g a).
Proof.
intros.
induction H as (x, p).
simpl in p.
assert (isPR 2 (fun a b : nat => a)).
apply pi1_2IsPR.
induction H as (x0, p0).
simpl in p0.
exists (composeFunc _ _ (PRcons _ _ x0 (PRnil _)) x).
simpl in |- *.
intros.
replace (g c) with (g (evalPrimRec 2 x0 c c0)).
rewrite <- p.
auto.
rewrite p0.
auto.

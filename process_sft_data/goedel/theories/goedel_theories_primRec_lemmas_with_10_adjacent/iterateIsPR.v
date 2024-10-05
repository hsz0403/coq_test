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

Lemma reduce1stCompose : forall (c n m : nat) (v : Vector.t (naryFunc n) m) (g : naryFunc (S m)), extEqual n (evalComposeFunc n _ (Vector.cons (naryFunc n) (evalConstFunc n c) _ v) g) (evalComposeFunc n _ v (g c)).
Proof.
intros c n.
induction n as [| n Hrecn].
simpl in |- *.
auto.
simpl in |- *.
fold (naryFunc n) in |- *.
intros.
Admitted.

Lemma reduce2ndCompose : forall (c n m : nat) (v : Vector.t (naryFunc n) m) (n0 : naryFunc n) (g : naryFunc (S (S m))), extEqual n (evalComposeFunc n _ (Vector.cons (naryFunc n) n0 _ (Vector.cons (naryFunc n) (evalConstFunc n c) _ v)) g) (evalComposeFunc n _ (Vector.cons (naryFunc n) n0 _ v) (fun x : nat => g x c)).
Proof.
intros c n.
induction n as [| n Hrecn].
simpl in |- *.
auto.
simpl in |- *.
fold (naryFunc n) in |- *.
intros.
Admitted.

Lemma evalPrimRecParam : forall (n c d : nat) (g : naryFunc (S n)) (h : naryFunc (S (S (S n)))), extEqual _ (evalPrimRecFunc n (g d) (fun x y : nat => h x y d) c) (evalPrimRecFunc (S n) g h c d).
Proof.
intros.
induction c as [| c Hrecc].
simpl in |- *.
apply extEqualRefl.
simpl in |- *.
apply extEqualCompose2.
auto.
Admitted.

Lemma compose2IsPR : forall (n : nat) (f : naryFunc n) (p : isPR n f) (g : naryFunc (S n)) (q : isPR (S n) g), isPR n (compose2 n f g).
Proof.
intros.
induction p as (x, p).
induction q as (x0, p0).
exists (composeFunc _ _ (PRcons _ _ x (projectionListPR n n (le_n n))) x0).
simpl in |- *.
apply extEqualTrans with (evalComposeFunc n (S n) (Vector.cons (naryFunc n) f n (evalPrimRecs n n (projectionListPR n n (le_n n)))) g).
apply extEqualCompose.
unfold extEqualVector in |- *.
simpl in |- *.
split.
auto.
apply extEqualVectorRefl.
auto.
clear p0 x0 p x.
induction n as [| n Hrecn].
simpl in |- *.
auto.
simpl in |- *.
fold (naryFunc n) in |- *.
induction (eq_nat_dec n n).
intros.
apply extEqualTrans with (evalComposeFunc n (S (S n)) (Vector.cons (naryFunc n) (f c) (S n) (Vector.cons (naryFunc n) (evalConstFunc n c) n (projectionList n n (le_n n)))) g).
apply extEqualSym.
apply extEqualCompose.
unfold extEqualVector in |- *.
simpl in |- *.
repeat split.
apply extEqualRefl.
apply extEqualRefl.
apply (projectionListApplyParam n n c (le_n n) (le_S_n n (S n) (le_S (S n) (S n) (le_n (S n))))).
apply extEqualRefl.
apply extEqualTrans with (evalComposeFunc n (S n) (Vector.cons (naryFunc n) (f c) n (evalPrimRecs n n (projectionListPR n n (le_n n)))) (fun x : nat => g x c)).
clear a Hrecn.
generalize (f c).
fold (naryFunc n) in |- *.
fold (projectionList n n (le_n n)) in |- *.
generalize (projectionList n n (le_n n)).
intros.
apply (reduce2ndCompose c n n t n0).
apply Hrecn.
elim b.
Admitted.

Lemma compose1_NIsPR : forall (n : nat) (g : naryFunc (S n)), isPR (S n) g -> forall f : naryFunc 1, isPR 1 f -> isPR (S n) (fun x : nat => g (f x)).
Proof.
intros.
induction H as (x, p).
induction H0 as (x0, p0).
exists (composeFunc (S n) (S n) (PRcons _ _ (composeFunc (S n) 1 (PRcons _ _ (projFunc (S n) n (lt_n_Sn n)) (PRnil _)) x0) (projectionListPR (S n) n (le_n_Sn n))) x).
simpl in |- *.
fold (naryFunc n) in |- *.
induction (eq_nat_dec n n).
intros.
apply extEqualTrans with (evalComposeFunc n (S n) (Vector.cons (naryFunc n) (evalConstFunc n (f c)) n (projectionList n n (le_n n))) g).
apply extEqualSym.
apply extEqualCompose.
unfold extEqualVector in |- *.
simpl in |- *.
split.
apply extEqualSym.
apply extEqualTrans with (evalComposeFunc n 1 (Vector.cons (naryFunc n) (evalConstFunc n c) 0 (Vector.nil (naryFunc n))) f).
apply extEqualCompose.
apply extEqualVectorRefl.
auto.
clear a p0 x0 p x g.
induction n as [| n Hrecn].
simpl in |- *.
reflexivity.
simpl in |- *.
intros.
apply Hrecn.
apply (projectionListApplyParam n n c (le_n n) (le_n_Sn n)).
apply extEqualSym.
auto.
clear p0 x0 p x a.
eapply extEqualTrans.
apply reduce1stCompose.
apply extEqualSym.
apply (projectionListId n (g (f c)) (le_n n)).
elim b.
Admitted.

Definition switchPR : naryFunc 3.
simpl in |- *.
intros.
destruct H as [| n].
apply H1.
Admitted.

Lemma switchIsPR : isPR 3 switchPR.
Proof.
intros.
assert (isPR 3 (fun a b c : nat => nat_rec (fun _ : nat => nat) c (fun (n : nat) (_ : (fun _ : nat => nat) n) => b) a)).
apply ind2ParamIsPR with (f := fun _ _ b c : nat => b) (g := fun b c : nat => c).
apply pi3_4IsPR.
apply pi2_2IsPR.
induction H as (x, p).
exists x.
apply extEqualTrans with (fun a b c : nat => nat_rec (fun _ : nat => nat) c (fun _ _ : nat => b) a).
apply p.
unfold switchPR in |- *.
simpl in |- *.
intros.
Admitted.

Lemma boundedSearch1 : forall (P : naryRel 2) (b x : nat), x < boundedSearch P b -> P b x = false.
Proof.
unfold boundedSearch in |- *.
intros P b.
generalize (P b).
intros b0 x H.
clear P.
induction b as [| b Hrecb].
simpl in H.
elim (lt_n_O _ H).
simpl in H.
induction (eq_nat_dec (boundedSearchHelp b0 b) b).
rewrite a in Hrecb.
induction (eq_nat_dec x b).
rewrite a0.
induction (b0 b).
elim (lt_irrefl b).
rewrite a0 in H.
auto.
auto.
apply Hrecb.
induction (b0 b).
auto.
assert (x <= b).
apply lt_n_Sm_le.
auto.
induction (le_lt_or_eq _ _ H0).
auto.
elim b1.
auto.
apply Hrecb.
Admitted.

Lemma boundedSearch2 : forall (P : naryRel 2) (b : nat), boundedSearch P b = b \/ P b (boundedSearch P b) = true.
Proof.
unfold boundedSearch in |- *.
intros P b.
assert (forall P : naryRel 1, boundedSearchHelp P b = b \/ P (boundedSearchHelp P b) = true).
clear P.
intros.
induction b as [| b Hrecb].
simpl in |- *.
auto.
simpl in |- *.
assert (P b = true \/ P b = false).
induction (P b); auto.
induction (eq_nat_dec (boundedSearchHelp P b) b).
induction H as [H| H].
rewrite H.
rewrite H.
auto.
rewrite H.
auto.
induction Hrecb as [H0| H0].
elim b0.
auto.
auto.
Admitted.

Lemma boundSearchIsPR : forall P : naryRel 2, isPRrel 2 P -> isPR 1 (fun b : nat => boundedSearch P b).
Proof.
intros.
unfold boundedSearch in |- *.
assert (isPR 2 (fun b c : nat => nat_rec (fun _ : nat => nat) 0 (fun b0 Hrecb : nat => sumbool_rec (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat) (fun _ : Hrecb = b0 => bool_rec (fun _ : bool => nat) b0 (S b0) (P c b0)) (fun _ : Hrecb <> b0 => Hrecb) (eq_nat_dec Hrecb b0)) b)).
apply ind1ParamIsPR with (g := fun _ : nat => 0) (f := fun b0 Hrecb c : nat => sumbool_rec (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat) (fun _ : Hrecb = b0 => bool_rec (fun _ : bool => nat) b0 (S b0) (P c b0)) (fun _ : Hrecb <> b0 => Hrecb) (eq_nat_dec Hrecb b0)).
unfold isPRrel in H.
assert (isPR 3 (fun b0 Hrecb c : nat => switchPR (charFunction 2 beq_nat Hrecb b0) (bool_rec (fun _ : bool => nat) b0 (S b0) (P c b0)) Hrecb)).
apply compose3_3IsPR with (g := switchPR) (f1 := fun b0 Hrecb c : nat => charFunction 2 beq_nat Hrecb b0) (f2 := fun b0 Hrecb c : nat => bool_rec (fun _ : bool => nat) b0 (S b0) (P c b0)) (f3 := fun b0 Hrecb c : nat => Hrecb).
apply filter110IsPR with (g := fun b0 Hrecb : nat => charFunction 2 beq_nat Hrecb b0).
apply swapIsPR.
apply eqIsPR.
apply filter101IsPR with (g := fun b0 c : nat => bool_rec (fun _ : bool => nat) b0 (S b0) (P c b0)).
assert (isPR 2 (fun b0 c : nat => switchPR (charFunction 2 P c b0) b0 (S b0))).
apply compose2_3IsPR with (g := switchPR) (f1 := fun b0 c : nat => charFunction 2 P c b0) (f2 := fun b0 c : nat => b0) (f3 := fun b0 c : nat => S b0).
apply swapIsPR.
apply H.
apply pi1_2IsPR.
apply filter10IsPR.
apply succIsPR.
apply switchIsPR.
induction H0 as (x, p).
exists x.
apply extEqualTrans with (fun b0 c : nat => switchPR (charFunction 2 P c b0) b0 (S b0)).
auto.
simpl in |- *.
intros.
induction (P c0 c); reflexivity.
apply pi2_3IsPR.
apply switchIsPR.
induction H0 as (x, p).
exists x.
apply extEqualTrans with (fun b0 Hrecb c : nat => switchPR (charFunction 2 beq_nat Hrecb b0) (bool_rec (fun _ : bool => nat) b0 (S b0) (P c b0)) Hrecb).
auto.
simpl in |- *.
intros.
induction (eq_nat_dec c0 c).
simpl in |- *.
rewrite <- a.
rewrite <- beq_nat_refl.
simpl in |- *.
reflexivity.
rewrite beq_nat_not_refl.
simpl in |- *.
reflexivity.
auto.
apply const1_NIsPR.
assert (isPR 1 (fun b : nat => nat_rec (fun _ : nat => nat) 0 (fun b0 Hrecb : nat => sumbool_rec (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat) (fun _ : Hrecb = b0 => bool_rec (fun _ : bool => nat) b0 (S b0) (P b b0)) (fun _ : Hrecb <> b0 => Hrecb) (eq_nat_dec Hrecb b0)) b)).
apply compose1_2IsPR with (g := fun b c : nat => nat_rec (fun _ : nat => nat) 0 (fun b0 Hrecb : nat => sumbool_rec (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat) (fun _ : Hrecb = b0 => bool_rec (fun _ : bool => nat) b0 (S b0) (P c b0)) (fun _ : Hrecb <> b0 => Hrecb) (eq_nat_dec Hrecb b0)) b) (f := fun b : nat => b) (f' := fun b : nat => b).
apply idIsPR.
apply idIsPR.
auto.
clear H0.
induction H1 as (x, p).
exists x.
apply extEqualTrans with (fun b : nat => nat_rec (fun _ : nat => nat) 0 (fun b0 Hrecb : nat => sumbool_rec (fun _ : {Hrecb = b0} + {Hrecb <> b0} => nat) (fun _ : Hrecb = b0 => bool_rec (fun _ : bool => nat) b0 (S b0) (P b b0)) (fun _ : Hrecb <> b0 => Hrecb) (eq_nat_dec Hrecb b0)) b).
auto.
clear H x p.
simpl in |- *.
intros.
generalize (P c).
intros b.
clear P.
induction c as [| c Hrecc].
simpl in |- *.
auto.
simpl in |- *.
rewrite Hrecc.
induction (eq_nat_dec (boundedSearchHelp b c) c).
simpl in |- *.
induction (b c).
auto.
auto.
simpl in |- *.
Admitted.

Lemma iterateIsPR : forall g : nat -> nat, isPR 1 g -> forall n : nat, isPR 1 (iterate g n).
Proof.
intros.
induction n as [| n Hrecn]; simpl in |- *.
apply idIsPR.
apply compose1_1IsPR; assumption.

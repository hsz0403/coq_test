Require Import Sets.
Inductive Un : Set := void : Un.
Inductive F : Set :=.
Definition Vide : Ens := sup F (fun f : F => match f return Ens with end).
Definition Paire : forall E E' : Ens, Ens.
intros.
apply (sup bool).
simple induction 1.
exact E.
exact E'.
Defined.
Hint Resolve Paire_sound_right Paire_sound_left: zfc.
Hint Resolve IN_Paire_left IN_Paire_right Vide_est_vide: zfc.
Definition Sing (E : Ens) := Paire E E.
Hint Resolve IN_Sing IN_Sing_EQ: zfc.
Hint Resolve Sing_sound: zfc.
Hint Resolve EQ_Sing_EQ: zfc.
Inductive sig (A : Type) (P : A -> Prop) : Type := exist : forall x : A, P x -> sig A P.
Definition Comp : Ens -> (Ens -> Prop) -> Ens.
simple induction 1; intros A f fr P.
apply (sup (sig A (fun x => P (f x)))).
simple induction 1; intros x p; exact (f x).
Defined.
Definition pi1 : Ens -> Type.
simple induction 1.
intros A f r.
exact A.
Defined.
Definition pi2 : forall E : Ens, pi1 E -> Ens.
simple induction E.
intros A f r.
exact f.
Defined.
Definition Union : forall E : Ens, Ens.
simple induction 1; intros A f r.
apply (sup (depprod A (fun x : A => pi1 (f x)))).
simple induction 1; intros a b.
exact (pi2 (f a) b).
Defined.
Definition Inter (E : Ens) : Ens := match E with | sup A f => sup _ (fun c : depprod _ (fun a : A => depprod _ (fun b : pi1 (f a) => forall x : A, IN (pi2 (f a) b) (f x))) => match c with | dep_i a (dep_i b p) => pi2 (f a) b end) end.
Definition Inter' (E : Ens) : Ens := Comp (Union E) (fun e : Ens => forall a : Ens, IN a E -> IN e a).
Definition Power (E : Ens) : Ens := match E with | sup A f => sup _ (fun P : A -> Prop => sup _ (fun c : depprod A (fun a : A => P a) => match c with | dep_i a p => f a end)) end.

Theorem all_IN_Inter : forall E E' E'' : Ens, IN E'' E -> (forall E'' : Ens, IN E'' E -> IN E' E'') -> IN E' (Inter E).
simple induction E; intros A f r.
intros E' E'' i H.
elim (IN_EXType (sup A f) E'' i).
intros a e; simpl in a.
simpl in e.
cut (IN E' E''); auto with zfc.
intros i'.
cut (IN E' (f a)); auto with zfc.
intros i0.
elim (IN_EXType (f a) E' i0).
intros b e'.
simpl in |- *.
cut (forall x : A, IN (pi2 (f a) b) (f x)).
intros.
exists (dep_i A (fun a : A => depprod (pi1 (f a)) (fun b : pi1 (f a) => forall x : A, IN (pi2 (f a) b) (f x))) a (dep_i (pi1 (f a)) (fun b : pi1 (f a) => forall x : A, IN (pi2 (f a) b) (f x)) b H0)).
simpl in |- *.
auto with zfc.
auto with zfc.
intros.
apply IN_sound_left with E'.
auto with zfc.
apply H.
auto with zfc.
simpl in |- *.
exists x; auto with zfc.
apply IN_sound_right with E''; auto with zfc.

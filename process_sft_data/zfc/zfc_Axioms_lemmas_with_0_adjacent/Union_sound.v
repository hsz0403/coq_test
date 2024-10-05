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

Theorem Union_sound : forall E E' : Ens, EQ E E' -> EQ (Union E) (Union E').
unfold Union in |- *; simple induction E; intros A f r; simple induction E'; intros A' f' r'; simpl in |- *; simple induction 1; intros e1 e2; split.
intros x; elim x; intros a aa; elim (e1 a); intros a' ea.
elim (EQ_EXType (f a) (f' a') ea aa); intros aa' eaa.
exists (dep_i A' (fun x : A' => pi1 (f' x)) a' aa'); simpl in |- *; auto with zfc.
intros c'; elim c'; intros a' aa'; elim (e2 a'); intros a ea.
cut (EQ (f' a') (f a)).
2: auto with zfc.
intros ea'; elim (EQ_EXType (f' a') (f a) ea' aa'); intros aa eaa.
exists (dep_i A (fun x : A => pi1 (f x)) a aa); auto with zfc.

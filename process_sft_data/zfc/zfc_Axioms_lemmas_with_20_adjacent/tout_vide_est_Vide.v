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

Theorem Vide_est_vide : forall E : Ens, IN E Vide -> F.
unfold Vide in |- *; simpl in |- *; intros E H; cut False.
simple induction 1.
Admitted.

Definition Paire : forall E E' : Ens, Ens.
intros.
apply (sup bool).
simple induction 1.
exact E.
Admitted.

Theorem Paire_sound_left : forall A A' B : Ens, EQ A A' -> EQ (Paire A B) (Paire A' B).
unfold Paire in |- *.
simpl in |- *.
intros; split.
simple induction x.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y; simpl in |- *.
exists true; auto with zfc.
Admitted.

Theorem Paire_sound_right : forall A B B' : Ens, EQ B B' -> EQ (Paire A B) (Paire A B').
unfold Paire in |- *; simpl in |- *; intros; split.
simple induction x.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y.
exists true; auto with zfc.
Admitted.

Theorem IN_Paire_left : forall E E' : Ens, IN E (Paire E E').
Admitted.

Theorem IN_Paire_right : forall E E' : Ens, IN E' (Paire E E').
Admitted.

Theorem Paire_IN : forall E E' A : Ens, IN A (Paire E E') -> EQ A E \/ EQ A E'.
unfold Paire in |- *; simpl in |- *.
Admitted.

Theorem IN_Sing : forall E : Ens, IN E (Sing E).
Admitted.

Theorem IN_Sing_EQ : forall E E' : Ens, IN E (Sing E') -> EQ E E'.
Admitted.

Theorem Sing_sound : forall A A' : Ens, EQ A A' -> EQ (Sing A) (Sing A').
Admitted.

Theorem EQ_Sing_EQ : forall E1 E2 : Ens, EQ (Sing E1) (Sing E2) -> EQ E1 E2.
intros; cut (IN E1 (Sing E2)).
intros; auto with zfc.
Admitted.

Definition Comp : Ens -> (Ens -> Prop) -> Ens.
simple induction 1; intros A f fr P.
apply (sup (sig A (fun x => P (f x)))).
Admitted.

Theorem Comp_INC : forall (E : Ens) (P : Ens -> Prop), INC (Comp E P) E.
unfold Comp, INC in |- *; simple induction E; simpl in |- *; intros.
Admitted.

Theorem IN_Comp_P : forall (E A : Ens) (P : Ens -> Prop), (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) -> IN A (Comp E P) -> P A.
Admitted.

Theorem IN_P_Comp : forall (E A : Ens) (P : Ens -> Prop), (forall w1 w2 : Ens, P w1 -> EQ w1 w2 -> P w2) -> IN A E -> P A -> IN A (Comp E P).
simple induction E; simpl in |- *; intros B f HR A P H i; elim i; simpl in |- *; intros.
cut (P (f x)).
intros Pf.
exists (exist B (fun x : B => P (f x)) x Pf); simpl in |- *; auto with zfc.
Admitted.

Definition pi1 : Ens -> Type.
simple induction 1.
intros A f r.
Admitted.

Definition pi2 : forall E : Ens, pi1 E -> Ens.
simple induction E.
intros A f r.
Admitted.

Definition Union : forall E : Ens, Ens.
simple induction 1; intros A f r.
apply (sup (depprod A (fun x : A => pi1 (f x)))).
simple induction 1; intros a b.
Admitted.

Theorem EQ_EXType : forall E E' : Ens, EQ E E' -> forall a : pi1 E, EXType (pi1 E') (fun b : pi1 E' => EQ (pi2 E a) (pi2 E' b)).
simple induction E; intros A f r; simple induction E'; intros A' f' r'; simpl in |- *; simple induction 1; intros e1 e2 a.
Admitted.

Theorem IN_EXType : forall E E' : Ens, IN E' E -> EXType (pi1 E) (fun a : pi1 E => EQ E' (pi2 E a)).
simple induction E; simpl in |- *.
intros A f r.
simple induction 1; simpl in |- *.
intros.
Admitted.

Theorem IN_Union : forall E E' E'' : Ens, IN E' E -> IN E'' E' -> IN E'' (Union E).
simple induction E; intros A f r.
intros.
simpl in |- *.
elim (IN_EXType (sup A f) E' H).
intros x e.
cut (EQ (pi2 (sup A f) x) E'); auto with zfc.
intros e1.
cut (IN E'' (pi2 (sup A f) x)).
intros i1.
elim (IN_EXType _ _ i1).
intros x0 e2.
simpl in x0.
exists (dep_i A (fun x : A => pi1 (f x)) x x0).
simpl in |- *.
exact e2.
Admitted.

Theorem tout_vide_est_Vide : forall E : Ens, (forall E' : Ens, IN E' E -> F) -> EQ E Vide.
unfold Vide in |- *; simple induction E; simpl in |- *; intros A e H H0; split.
intros; elim (H0 (e x)); auto with zfc.
exists x; auto with zfc.
simple induction y.

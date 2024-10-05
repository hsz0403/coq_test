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

Theorem Union_IN : forall E E' : Ens, IN E' (Union E) -> EXType _ (fun E1 : Ens => IN E1 E /\ IN E' E1).
simple induction E; unfold Union in |- *; simpl in |- *; intros A f r.
simple induction 1.
simple induction x.
intros a b; simpl in |- *.
intros.
exists (f a).
split.
exists a; auto with zfc.
apply IN_sound_left with (pi2 (f a) b); auto with zfc.
simpl in |- *.
generalize b; elim (f a); simpl in |- *.
intros.
Admitted.

Theorem Union_sound : forall E E' : Ens, EQ E E' -> EQ (Union E) (Union E').
unfold Union in |- *; simple induction E; intros A f r; simple induction E'; intros A' f' r'; simpl in |- *; simple induction 1; intros e1 e2; split.
intros x; elim x; intros a aa; elim (e1 a); intros a' ea.
elim (EQ_EXType (f a) (f' a') ea aa); intros aa' eaa.
exists (dep_i A' (fun x : A' => pi1 (f' x)) a' aa'); simpl in |- *; auto with zfc.
intros c'; elim c'; intros a' aa'; elim (e2 a'); intros a ea.
cut (EQ (f' a') (f a)).
2: auto with zfc.
intros ea'; elim (EQ_EXType (f' a') (f a) ea' aa'); intros aa eaa.
Admitted.

Theorem Union_mon : forall E E' : Ens, INC E E' -> INC (Union E) (Union E').
unfold INC in |- *; intros E E' IEE E'' IEE''.
elim (Union_IN E E'').
intros E'''; simple induction 1; intros I1 I2.
apply IN_Union with E'''; auto with zfc.
Admitted.

Theorem IN_Inter_all : forall E E' : Ens, IN E' (Inter E) -> forall E'' : Ens, IN E'' E -> IN E' E''.
simple induction E; intros A f r; simpl in |- *; intros E'.
simple induction 1; intros c; elim c; intros a ca; elim ca; intros aa paa; simpl in |- *.
intros e E'' e''.
elim e''; intros a1 ea1.
apply IN_sound_right with (f a1); auto with zfc.
Admitted.

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
Admitted.

Theorem IN_Inter'_all : forall E E' : Ens, IN E' (Inter' E) -> forall E'' : Ens, IN E'' E -> IN E' E''.
unfold Inter' in |- *.
intros E E' i.
change ((fun e : Ens => forall a : Ens, IN a E -> IN e a) E') in |- *.
apply (IN_Comp_P (Union E) E').
intros.
apply IN_sound_left with w1; auto with zfc.
Admitted.

Theorem all_IN_Inter' : forall E E' E'' : Ens, IN E'' E -> (forall E'' : Ens, IN E'' E -> IN E' E'') -> IN E' (Inter' E).
unfold Inter' in |- *.
intros.
apply IN_P_Comp.
intros; apply IN_sound_left with w1; auto with zfc.
apply IN_Union with (E' := E''); auto with zfc.
Admitted.

Theorem IN_Power_INC : forall E E' : Ens, IN E' (Power E) -> INC E' E.
simple induction E.
intros A f r; unfold INC in |- *; simpl in |- *.
intros E'; simple induction 1; intros P.
elim E'; simpl in |- *.
intros A' f' r'.
simple induction 1; intros HA HB.
intros E''; simple induction 1; intros a' e.
elim (HA a').
simple induction x; intros a p.
intros; exists a.
auto with zfc.
Admitted.

Theorem INC_IN_Power : forall E E' : Ens, INC E' E -> IN E' (Power E).
simple induction E; intros A f r; unfold INC in |- *; simpl in |- *.
simple induction E'; intros A' f' r' i.
exists (fun a : A => IN (f a) (sup A' f')).
simpl in |- *.
split.
intros.
elim (i (f' x)); auto with zfc.
intros a e.
cut (EQ (f a) (f' x)); auto with zfc.
intros e1.
exists (dep_i A (fun a : A => EXType A' (fun y : A' => EQ (f a) (f' y))) a (EXTypei A' (fun y : A' => EQ (f a) (f' y)) x e1)).
simpl in |- *.
auto with zfc.
auto with zfc.
simpl in |- *.
exists x; auto with zfc.
simple induction y; simpl in |- *.
simple induction 1; intros.
Admitted.

Theorem Power_mon : forall E E' : Ens, INC E E' -> INC (Power E) (Power E').
intros.
unfold INC in |- *; intros.
apply INC_IN_Power.
cut (INC E0 E).
unfold INC in |- *; unfold INC in H; intros; auto with zfc.
Admitted.

Theorem IN_INC_Union : forall E E' : Ens, IN E' E -> INC E' (Union E).
unfold INC in |- *; simple induction E; intros A f r; unfold Union in |- *.
intros E' i E'' i'; simpl in |- *; elim (IN_EXType (sup A f) E' i).
intros a e; simpl in a; simpl in e.
elim (IN_EXType E' E'' i').
cut (IN E'' (f a)).
intros i'' a' e''; elim (IN_EXType _ _ i''); simpl in |- *; intros aa ee.
exists (dep_i A (fun x : A => pi1 (f x)) a aa); auto with zfc.
apply IN_sound_right with E'; auto with zfc.

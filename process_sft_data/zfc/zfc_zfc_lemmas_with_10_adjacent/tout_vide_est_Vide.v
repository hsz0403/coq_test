Set Asymmetric Patterns.
Inductive Ens : Type := sup : forall A : Type, (A -> Ens) -> Ens.
Inductive EXType (P : Type) (Q : P -> Prop) : Prop := EXTypei : forall x : P, Q x -> EXType P Q.
Inductive prod_t (A B : Type) : Type := pair_t : A -> B -> prod_t A B.
Inductive depprod (A : Type) (P : A -> Type) : Type := dep_i : forall x : A, P x -> depprod A P.
Definition EQ : Ens -> Ens -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType _ (fun x : A => eq1 x (g y))).
Defined.
Definition IN (E1 E2 : Ens) : Prop := match E2 with | sup A f => EXType _ (fun y : A => EQ E1 (f y)) end.
Definition INC : Ens -> Ens -> Prop.
intros E1 E2.
exact (forall E : Ens, IN E E1 -> IN E E2).
Defined.
Hint Resolve EQ_sym EQ_refl EQ_INC: zfc.
Hint Resolve INC_EQ: zfc.
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
Definition Power (E : Ens) : Ens := match E with | sup A f => sup _ (fun P : A -> Prop => sup _ (fun c : depprod A (fun a : A => P a) => match c with | dep_i a p => f a end)) end.
Definition Couple (E E' : Ens) := Paire (Sing E) (Paire Vide (Sing E')).
Definition Prod (E E' : Ens) : Ens := match E, E' with | sup A f, sup A' f' => sup _ (fun c : prod_t A A' => match c with | pair_t a a' => Couple (f a) (f' a') end) end.
Hint Resolve Paire_sound_left Paire_sound_right: zfc.
Definition Succ (E : Ens) := Union (Paire E (Sing E)).
Inductive Ord : Ens -> Prop := | Oo : Ord Vide | So : forall E : Ens, Ord E -> Ord (Succ E) | Lo : forall E : Ens, (forall e : Ens, IN e E -> Ord e) -> Ord (Union E) | Eo : forall E E' : Ens, Ord E -> EQ E E' -> Ord E'.
Hint Resolve Oo So Lo: zfc.
Definition Nat : nat -> Ens.
simple induction 1; intros.
exact Vide.
exact (Succ X).
Defined.
Definition Omega : Ens := sup nat Nat.
Hint Resolve IN_Succ INC_Succ: zfc.
Hint Resolve Nat_IN_Omega: zfc.
Definition Alpha : Ens -> Ens.
simple induction 1; intros A f r.
apply Union.
apply (sup A).
intros a.
exact (Power (r a)).
Defined.
Definition collection := forall P : Ens -> Ens -> Prop, (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) -> (forall E : Ens, EXType _ (P E)) -> forall E : Ens, EXType _ (fun A : Ens => forall x : Ens, IN x E -> EXType _ (fun y : Ens => IN y A /\ P x y)).
Definition choice := forall (A B : Type) (P : A -> B -> Prop), (forall a : A, EXType _ (fun b : B => P a b)) -> EXType _ (fun f : A -> B => forall a : A, P a (f a)).
Definition functional (P : Ens -> Ens -> Prop) := forall x y y' : Ens, P x y -> P x y' -> EQ y y'.
Definition replacement := forall P : Ens -> Ens -> Prop, functional P -> (forall x y y' : Ens, EQ y y' -> P x y -> P x y') -> (forall x x' y : Ens, EQ x x' -> P x y -> P x' y) -> forall X : Ens, EXType _ (fun Y : Ens => forall y : Ens, (IN y Y -> EXType _ (fun x : Ens => IN x X /\ P x y)) /\ (EXType _ (fun x : Ens => IN x X /\ P x y) -> IN y Y)).
Definition EQC : Ens -> Ens -> Type.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
refine (prod_t _ _).
exact (forall x : A, depprod _ (fun y : B => eq1 x (g y))).
exact (forall y : B, depprod _ (fun x : A => eq1 x (g y))).
Defined.
Definition CIN : Ens -> Ens -> Type.
simple induction 2.
intros.
exact (depprod _ (fun y : A => EQC X (e y))).
Defined.
Definition CINC : Ens -> Ens -> Type.
intros E1 E2.
exact (forall E : Ens, CIN E E1 -> CIN E E2).
Defined.
Hint Resolve EQC_sym EQC_refl EQC_INC: zfc.
Hint Resolve CINC_EQC: zfc.
Inductive sum_t (A B : Type) : Type := | inl_t : A -> sum_t A B | inr_t : B -> sum_t A B.
Hint Resolve inl_t inr_t: zfc.
Hint Resolve CIN_Paire_left CIN_Paire_right: zfc.
Inductive depprod' (A : Type) (P : A -> Type) : Type := dep_i' : forall x : A, P x -> depprod' A P.
Inductive Ens' : Type := sup' : forall A : Type, (A -> Ens') -> Ens'.
Inductive EXType' (P : Type) (Q : P -> Prop) : Prop := EXTypei' : forall x : P, Q x -> EXType' P Q.
Inductive prod_t' (A B : Type) : Type := pair_t' : A -> B -> prod_t' A B.
Inductive depprod'' (A : Type) (P : A -> Type) : Type := dep_i'' : forall x : A, P x -> depprod'' A P.
Definition EQ' : Ens' -> Ens' -> Prop.
simple induction 1; intros A f eq1.
simple induction 1; intros B g eq2.
apply and.
exact (forall x : A, EXType' _ (fun y : B => eq1 x (g y))).
exact (forall y : B, EXType' _ (fun x : A => eq1 x (g y))).
Defined.
Definition inj : Ens' -> Ens.
simple induction 1; intros A f fr.
exact (sup A fr).
Defined.
Definition Power' (E : Ens') : Ens' := match E with | sup' A f => sup' _ (fun P : A -> Prop => sup' _ (fun c : depprod'' A (fun a : A => P a) => match c with | dep_i'' a p => f a end)) end.
Definition Big := sup Ens' inj.

Theorem EQ_sym : forall E1 E2 : Ens, EQ E1 E2 -> EQ E2 E1.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2; simpl in |- *; simple induction 1; intros e1 e2; split.
intros a2; elim (e2 a2); intros a1 H1; exists a1; auto.
Admitted.

Theorem EQ_INC : forall E E' : Ens, EQ E E' -> INC E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r'; simpl in |- *; simple induction 1; intros e1 e2; unfold INC in |- *; simpl in |- *.
intros C; simple induction 1; intros a ea; elim (e1 a); intros a' ea'; exists a'.
Admitted.

Theorem INC_EQ : forall E E' : Ens, INC E E' -> INC E' E -> EQ E E'.
simple induction E; intros A f r; simple induction E'; intros A' f' r'; unfold INC in |- *; simpl in |- *; intros I1 I2; split.
intros a; apply I1.
exists a; auto with zfc.
intros a'; cut (EXType A (fun x : A => EQ (f' a') (f x))).
simple induction 1; intros a ea; exists a; auto with zfc.
Admitted.

Theorem IN_sound_left : forall E E' E'' : Ens, EQ E E' -> IN E E'' -> IN E' E''.
Admitted.

Theorem IN_sound_right : forall E E' E'' : Ens, EQ E' E'' -> IN E E' -> IN E E''.
Admitted.

Theorem INC_refl : forall E : Ens, INC E E.
Admitted.

Theorem INC_tran : forall E E' E'' : Ens, INC E E' -> INC E' E'' -> INC E E''.
Admitted.

Theorem INC_sound_left : forall E E' E'' : Ens, EQ E E' -> INC E E'' -> INC E' E''.
simple induction E''; unfold INC in |- *; simpl in |- *; intros A f HR e H1 E0 i; apply H1.
Admitted.

Theorem INC_sound_right : forall E E' E'' : Ens, EQ E' E'' -> INC E E' -> INC E E''.
simple induction E'; simple induction E''; unfold INC in |- *; simpl in |- *; intros.
elim (H2 E0); try assumption; intros.
elim H1; intros HA HB; elim (HA x); intros.
Admitted.

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

Theorem tout_vide_est_Vide : forall E : Ens, (forall E' : Ens, IN E' E -> F) -> EQ E Vide.
unfold Vide in |- *; simple induction E; simpl in |- *; intros A e H H0; split.
intros; elim (H0 (e x)); auto with zfc.
exists x; auto with zfc.
simple induction y.

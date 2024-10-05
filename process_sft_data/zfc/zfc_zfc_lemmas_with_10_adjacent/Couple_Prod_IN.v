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

Theorem Power_sound : forall E E' : Ens, EQ E E' -> EQ (Power E) (Power E').
intros E E' e.
apply INC_EQ; unfold INC in |- *.
intros A i.
cut (INC A E').
intros; apply INC_IN_Power; assumption.
cut (INC A E); intros.
apply INC_sound_right with E; auto with zfc.
apply IN_Power_INC; assumption.
intros A i.
cut (INC A E).
intros; apply INC_IN_Power; assumption.
cut (INC A E'); intros.
apply INC_sound_right with E'; auto with zfc.
Admitted.

Theorem not_EQ_Sing_Vide : forall E : Ens, EQ (Sing E) Vide -> F.
intros E e; cut False.
simple induction 1.
cut (IN E Vide).
simpl in |- *; simple induction 1; intros xx; elim xx; simple induction 1.
Admitted.

Theorem not_EQ_Vide_Sing : forall E : Ens, EQ Vide (Sing E) -> F.
intros E e; cut False.
simple induction 1.
cut (IN E Vide).
simpl in |- *; simple induction 1; intros xx; elim xx; simple induction 1.
Admitted.

Theorem Couple_inj_left : forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A B.
unfold Couple in |- *; simpl in |- *.
simple induction 1.
intros HA HB; elim (HA true).
intros x; elim x; simpl in |- *; simple induction 1; intros H3 H4; elim (H3 true); simpl in |- *; intros xx; elim xx; simpl in |- *; auto with zfc.
elim (H4 false); simpl in |- *.
simple induction x0; simpl in |- *.
intros.
cut (EQ (Sing B') Vide).
simpl in |- *.
simple induction 1.
intros yy; elim (yy true).
simple induction x1.
apply EQ_tran with A; auto with zfc.
intros; cut (EQ (Sing B') Vide).
simpl in |- *.
simple induction 1.
intros yy; elim (yy true).
simple induction x1.
apply EQ_tran with A; auto with zfc.
intros yy.
elim (HB true); simpl in |- *.
simple induction x0.
change (EQ (Sing A) (Sing B) -> EQ A B) in |- *; intros EE.
apply IN_Sing_EQ.
apply IN_sound_right with (Sing A); auto with zfc.
change (EQ (Paire Vide (Sing A')) (Sing B) -> EQ A B) in |- *.
intros zz.
elimtype F.
apply (not_EQ_Sing_Vide A').
apply EQ_tran with B.
apply IN_Sing_EQ.
apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
Admitted.

Theorem Couple_inj_right : forall A A' B B' : Ens, EQ (Couple A A') (Couple B B') -> EQ A' B'.
unfold Couple in |- *; simpl in |- *.
simple induction 1; intros H1 H2.
elim (H1 false).
intros bb1; elim bb1.
intros HF.
change (EQ (Paire Vide (Sing A')) (Sing B)) in HF.
cut F.
simple induction 1.
apply (not_EQ_Vide_Sing A').
apply EQ_tran with B.
apply IN_Sing_EQ; apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
apply EQ_sym; apply IN_Sing_EQ; apply IN_sound_right with (Paire Vide (Sing A')); auto with zfc.
change (EQ (Paire Vide (Sing A')) (Paire Vide (Sing B')) -> EQ A' B') in |- *.
intros HP; cut (EQ (Sing A') (Sing B')).
intros; auto with zfc.
cut (IN (Sing A') (Paire Vide (Sing B'))).
intros HI; elim (Paire_IN Vide (Sing B') (Sing A') HI).
intros; cut F.
simple induction 1.
apply not_EQ_Sing_Vide with A'; assumption.
trivial with zfc.
Admitted.

Theorem Couple_sound_left : forall A A' B : Ens, EQ A A' -> EQ (Couple A B) (Couple A' B).
Admitted.

Theorem Couple_sound_right : forall A B B' : Ens, EQ B B' -> EQ (Couple A B) (Couple A B').
Admitted.

Theorem Couple_IN_Prod : forall E1 E2 E1' E2' : Ens, IN E1' E1 -> IN E2' E2 -> IN (Couple E1' E2') (Prod E1 E2).
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2.
intros E1' E2' i1 i2.
elim (IN_EXType (sup A1 f1) E1').
intros x e1; simpl in x.
elim (IN_EXType (sup A2 f2) E2').
intros x0 e2; simpl in x.
apply IN_sound_left with (Couple (pi2 (sup A1 f1) x) (pi2 (sup A2 f2) x0)); auto with zfc.
apply EQ_tran with (Couple (pi2 (sup A1 f1) x) E2'); auto with zfc.
apply Couple_sound_right.
auto with zfc.
apply Couple_sound_left; auto with zfc.
simpl in |- *.
simpl in |- *.
exists (pair_t _ _ x x0).
simpl in |- *.
split.
simple induction x1; simpl in |- *.
exists true; simpl in |- *.
split.
simple induction x2; simpl in |- *.
exists true; auto with zfc.
exists true; auto with zfc.
simple induction y; exists true; auto with zfc.
exists false; simpl in |- *.
split.
simple induction x2.
exists true; simpl in |- *; auto with zfc.
split.
simple induction x3.
simple induction y.
exists false; auto with zfc.
simple induction y; simpl in |- *.
exists true; auto with zfc.
exists false; auto with zfc.
simple induction y; simpl in |- *.
exists true; auto with zfc.
exists false; auto with zfc.
auto with zfc.
Admitted.

Theorem IN_Prod_EXType : forall E E' E'' : Ens, IN E'' (Prod E E') -> EXType _ (fun A : Ens => EXType _ (fun B : Ens => EQ (Couple A B) E'')).
simple induction E; intros A f r; simple induction E'; intros A' f' r'.
intros; elim (IN_EXType (Prod (sup A f) (sup A' f')) E'').
simple induction x.
intros; exists (f a); exists (f' b); auto with zfc.
Admitted.

Definition Nat : nat -> Ens.
simple induction 1; intros.
exact Vide.
Admitted.

Theorem Nat_Ord : forall n : nat, Ord (Nat n).
Admitted.

Theorem IN_Succ : forall E : Ens, IN E (Succ E).
Admitted.

Theorem INC_Succ : forall E : Ens, INC E (Succ E).
unfold INC in |- *; unfold Succ in |- *.
intros.
Admitted.

Theorem IN_Succ_or : forall E E' : Ens, IN E' (Succ E) -> EQ E E' \/ IN E' E.
intros E E' i.
unfold Succ in i.
elim (Union_IN (Paire E (Sing E)) E' i).
intros E1; simple induction 1; intros i1 i2.
elim (Paire_IN E (Sing E) E1 i1).
intros; right; apply IN_sound_right with E1; auto with zfc.
intros; left; cut (IN E' (Sing E)).
auto with zfc.
Admitted.

Theorem E_not_IN_E : forall E : Ens, IN E E -> F.
simple induction E; intros A f r i.
cut False.
simple induction 1.
elim (IN_EXType (sup A f) (sup A f) i); intros a e.
simpl in a.
change (EQ (sup A f) (f a)) in e.
elim (r a).
apply IN_sound_right with (sup A f); auto with zfc.
Admitted.

Theorem Nat_IN_Omega : forall n : nat, IN (Nat n) Omega.
Admitted.

Theorem IN_Omega_EXType : forall E : Ens, IN E Omega -> EXType _ (fun n : nat => EQ (Nat n) E).
simpl in |- *; simple induction 1.
intros n e.
Admitted.

Theorem IN_Nat_EXType : forall (n : nat) (E : Ens), IN E (Nat n) -> EXType _ (fun p : nat => EQ E (Nat p)).
simple induction n.
simpl in |- *.
simple induction 1.
simple induction x.
intros.
change (IN E (Succ (Nat n0))) in H0.
elim (IN_Succ_or (Nat n0) E H0).
intros; exists n0.
auto with zfc.
intros.
Admitted.

Theorem Couple_Prod_IN : forall E1 E2 E1' E2' : Ens, IN (Couple E1' E2') (Prod E1 E2) -> IN E1' E1 /\ IN E2' E2.
simple induction E1; intros A1 f1 r1; simple induction E2; intros A2 f2 r2.
intros E1' E2' i.
elim (IN_EXType (Prod (sup A1 f1) (sup A2 f2)) (Couple E1' E2') i).
intros xx; elim xx; intros a1 a2 e.
change (EQ (Couple E1' E2') (Couple (f1 a1) (f2 a2))) in e.
cut (EQ E1' (f1 a1)).
cut (EQ E2' (f2 a2)).
intros e1 e2.
split.
apply IN_sound_left with (f1 a1); auto with zfc; simpl in |- *; exists a1; auto with zfc.
apply IN_sound_left with (f2 a2); auto with zfc; simpl in |- *; exists a2; auto with zfc.
apply Couple_inj_right with (A := E1') (B := f1 a1); auto with zfc.
apply Couple_inj_left with E2' (f2 a2); auto with zfc.

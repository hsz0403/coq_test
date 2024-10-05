Set Asymmetric Patterns.
Definition si (X : Set) (b : bool) (x y : X) := match b with | true => x | _ => y end.
Fixpoint egal_nat (n : nat) : nat -> bool := fun m : nat => match n, m with | O, O => true | S n, S m => egal_nat n m | _, _ => false end.
Fixpoint inf_egal (n : nat) : nat -> bool := fun m : nat => match n, m with | O, m => true | S n, O => false | S n, S m => inf_egal n m end.
Inductive list (X : Set) : Set := | Nil : list X | Cons : X -> list X -> list X.
Definition cdr (X : Set) (l : list X) := match l with | Nil => Nil X | Cons _ xs => xs end.
Fixpoint length (X : Set) (l : list X) {struct l} : nat := match l with | Nil => 0 | Cons _ xs => S (length X xs) end.
Fixpoint append (X : Set) (ys xs : list X) {struct xs} : list X := match xs with | Nil => ys | Cons x xs' => Cons X x (append X ys xs') end.
Fixpoint sorted (l : list nat) : Prop := match l with | Cons n (Cons m x as l) => inf_egal n m = true /\ sorted l | _ => True end.
Fixpoint nocc (n : nat) (l : list nat) {struct l} : nat := match l with | Nil => 0 | Cons m x => si nat (egal_nat n m) (S (nocc n x)) (nocc n x) end.
Fixpoint ins (n : nat) (l : list nat) {struct l} : list nat := match l with | Nil => Cons nat n (Nil nat) | Cons m x => si (list nat) (inf_egal n m) (Cons nat n (Cons nat m x)) (Cons nat m (ins n x)) end.
Fixpoint tri_ins (l : list nat) : list nat := match l with | Nil => Nil nat | Cons n x => ins n (tri_ins x) end.
Fixpoint bubble_aux (x : list nat) : nat -> list nat := fun n : nat => match x with | Nil => Cons nat n (Nil nat) | Cons n0 l => si (list nat) (inf_egal n n0) (Cons nat n (bubble_aux l n0)) (Cons nat n0 (bubble_aux l n)) end.
Definition bubble (x : list nat) : list nat := match x with | Nil => Nil nat | Cons n l => bubble_aux l n end.
Fixpoint bubble_sort0 (n : nat) : list nat -> list nat := fun x : list nat => match n with | O => x | S n0 => bubble_sort0 n0 (bubble x) end.
Definition bubble_sort (x : list nat) : list nat := bubble_sort0 (length nat x) x.
Fixpoint fusion (x : list nat) : list nat -> list nat := fun y : list nat => match x with | Nil => y | Cons n l0 => (fix fusion_r (y : list nat) : list nat := match y with | Nil => x | Cons n0 l2 => si (list nat) (inf_egal n n0) (Cons nat n (fusion l0 (Cons nat n0 l2))) (Cons nat n0 (fusion_r l2)) end) y end.
Fixpoint tri_merge0 (n : nat) : list (list nat) -> list nat := fun ll : list (list nat) => match n, ll with | S l, Cons ns Nil => ns | S l, Cons ns (Cons ms xss) => fusion (fusion ns ms) (tri_merge0 l xss) | _, _ => Nil nat end.
Fixpoint l2ll (X : Set) (l : list X) {struct l} : list (list X) := match l with | Nil => Nil (list X) | Cons x xs => Cons (list X) (Cons X x (Nil X)) (l2ll X xs) end.
Definition tri_merge (l : list nat) : list nat := tri_merge0 (length nat l) (l2ll nat l).
Inductive arbin : Set := | Fe : arbin | Br : nat -> arbin -> arbin -> arbin.
Fixpoint abr2Ln (a : arbin) : list nat := match a with | Fe => Nil nat | Br n a1 a2 => append nat (Cons nat n (abr2Ln a2)) (abr2Ln a1) end.
Fixpoint insabr (n : nat) (a : arbin) {struct a} : arbin := match a with | Fe => Br n Fe Fe | Br m a1 a2 => si arbin (inf_egal n m) (Br m (insabr n a1) a2) (Br m a1 (insabr n a2)) end.
Fixpoint Ln2abr (l : list nat) : arbin := match l with | Nil => Fe | Cons n ns => insabr n (Ln2abr ns) end.
Definition tri_abr (ns : list nat) : list nat := abr2Ln (Ln2abr ns).
Fixpoint Tas2Ln (a : arbin) : list nat := match a with | Fe => Nil nat | Br n a1 a2 => Cons nat n (fusion (Tas2Ln a1) (Tas2Ln a2)) end.
Fixpoint insTas (n : nat) (a : arbin) {struct a} : arbin := match a with | Fe => Br n Fe Fe | Br m a1 a2 => si arbin (inf_egal n m) (Br n a2 (insTas m a1)) (Br m a2 (insTas n a1)) end.
Fixpoint Ln2Tas (l : list nat) : arbin := match l with | Nil => Fe | Cons n ns => insTas n (Ln2Tas ns) end.
Definition tri_heap (l : list nat) : list nat := Tas2Ln (Ln2Tas l).

Lemma si_eq1 : forall (X : Set) (x y : X), si X true x y = x.
Proof.
Admitted.

Lemma si_eq2 : forall (X : Set) (x y : X), si X false x y = y.
Proof.
Admitted.

Lemma inf_egal_eq2 : forall n : nat, inf_egal (S n) 0 = false.
Proof.
Admitted.

Lemma inf_egal_eq3 : forall n m : nat, inf_egal (S n) (S m) = inf_egal n m.
Proof.
Admitted.

Lemma sorted_eq1 : sorted (Nil nat) = True.
Proof.
Admitted.

Lemma sorted_eq2 : forall n : nat, sorted (Cons nat n (Nil nat)) = True.
Proof.
Admitted.

Lemma sorted_eq3 : forall (n m : nat) (x : list nat), sorted (Cons nat n (Cons nat m x)) = (inf_egal n m = true /\ sorted (Cons nat m x)).
Proof.
Admitted.

Lemma nocc_eq1 : forall n : nat, nocc n (Nil nat) = 0.
Proof.
Admitted.

Lemma nocc_eq2 : forall (n m : nat) (x : list nat), nocc n (Cons nat m x) = si nat (egal_nat n m) (S (nocc n x)) (nocc n x).
Proof.
Admitted.

Theorem diff_true_false : true <> false.
Proof.
Admitted.

Theorem si_intro : forall (X : Set) (P : X -> Prop) (x y : X) (b : bool), (b = true :>bool -> P x) -> (b = false :>bool -> P y) -> P (si X b x y).
Proof.
simple induction b.
intros.
rewrite si_eq1.
apply H.
trivial.
intros.
rewrite si_eq2.
apply H0.
Admitted.

Theorem inf_false_true : forall n m : nat, inf_egal n m = false -> inf_egal m n = true.
Proof.
simple induction n.
intros.
apply False_ind.
apply diff_true_false.
assumption.
simple induction m.
intro.
trivial.
intros.
rewrite inf_egal_eq3.
apply H.
Admitted.

Lemma inf_egal_eq1 : forall m : nat, inf_egal 0 m = true.
Proof.
auto.

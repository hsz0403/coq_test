Require Export List.
Export ListNotations.
Require Export Arith.
Require Import Inverse_Image.
Require Import Wf_nat.
Section Minus.
End Minus.
Hint Resolve le_minus: arith.
Section LeBool.
Fixpoint le_bool (a b : nat) {struct b} : bool := match a, b with | O, _ => true | S a1, S b1 => le_bool a1 b1 | _, _ => false end.
End LeBool.
Section Fold.
Variables (A : Type) (B : Type).
Variable f : A -> B -> A.
Variable g : B -> A -> A.
Variable h : A -> A.
End Fold.
Section List.
Variables (A : Type) (B : Type) (C : Type).
Variable f : A -> B.
Program Definition list_length_induction (P : list A -> Type) (rec: forall l1 : list A, (forall l2 : list A, length l2 < length l1 -> P l2) -> P l1) (l : list A) : P l := @well_founded_induction_type _ (fun x y : list A => length x < length y) ((fun _ _ _ => @wf_inverse_image _ _ lt _ _) P rec l) P rec l.
End List.
Section map2.
Variables (A : Type) (B : Type) (C : Type).
Variable f : A -> B -> C.
Fixpoint map2 (l1 : list A) : list B -> list C := fun l2 => match l1 with | [] => [] | a :: l3 => match l2 with | [] => [] | b :: l4 => f a b :: map2 l3 l4 end end.
End map2.
Arguments map2 [A B C].
Section First.
Variable A : Type.
End First.
Section FirstMax.
End FirstMax.
Section FindMin.
Variable A : Type.
Variable f : A -> nat.
Fixpoint find_min (l : list A) : option (nat * A) := match l with | [] => None | a :: l1 => match find_min l1 with | None => Some (f a, a) | Some (n1, b) => let n2 := f a in match le_lt_dec n1 n2 with | left _ => Some (n1, b) | right _ => Some (n2, a) end end end.
Fixpoint find_max (l : list A) : option (nat * A) := match l with | [] => None | a :: l1 => match find_max l1 with | None => Some (f a, a) | Some (n1, b) => let n2 := f a in match le_lt_dec n1 n2 with | right _ => Some (n1, b) | left _ => Some (n2, a) end end end.
End FindMin.
Arguments find_min [A].
Arguments find_max [A].

Theorem le_minus : forall a b : nat, a - b <= a.
Proof using.
intros a; elim a; simpl in |- *; auto.
Admitted.

Theorem minus_minus_simpl4 : forall a b c : nat, b <= c -> c <= a -> a - b - (a - c) = c - b.
Proof using.
intros a b c H H0.
apply plus_minus; auto with arith.
rewrite minus_plus_simpl_l_reverse with (p := b + c).
repeat rewrite plus_assoc_reverse.
rewrite <- le_plus_minus; auto with arith.
repeat rewrite plus_assoc.
rewrite (plus_comm b c).
repeat rewrite plus_assoc_reverse.
rewrite <- le_plus_minus; auto with arith.
repeat rewrite (fun x => plus_comm x a).
rewrite <- minus_plus_simpl_l_reverse; auto with arith.
Admitted.

Theorem plus_minus_simpl4 : forall a b c : nat, b <= a -> c <= b -> a - b + (b - c) = a - c.
Proof using.
intros a b c H H0.
apply plus_minus.
rewrite (fun x y => plus_comm (x - y)).
rewrite plus_assoc.
rewrite <- le_plus_minus; auto.
Admitted.

Theorem le_bool_correct1 : forall a b : nat, a <= b -> le_bool a b = true.
Proof using.
intros a; elim a; simpl in |- *; auto.
intros b; case b; simpl in |- *; auto.
intros n H b; case b; simpl in |- *.
intros H1; inversion H1.
intros n0 H0; apply H.
Admitted.

Theorem le_bool_correct2 : forall a b : nat, b < a -> le_bool a b = false.
Proof using.
intros a; elim a; simpl in |- *; auto.
intros b H1; inversion H1.
intros n H b; case b; simpl in |- *; auto.
intros n0 H0; apply H.
Admitted.

Theorem le_bool_correct3 : forall a b : nat, le_bool a b = true -> a <= b.
Proof using.
intros a; elim a; simpl in |- *; auto.
intros b; case b; simpl in |- *; auto with arith.
Admitted.

Theorem le_bool_correct4 : forall a b : nat, le_bool a b = false -> b <= a.
Proof using.
intros a; elim a; simpl in |- *; auto.
intros b; case b; simpl in |- *; try (intros; discriminate); auto with arith.
Admitted.

Theorem fold_left_eta : forall l a f1, (forall a b, In b l -> f a b = f1 a b) -> fold_left f l a = fold_left f1 l a.
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a l0 H a0 f1 H0.
Admitted.

Theorem fold_left_map : forall (C : Type) a l (k : C -> B), fold_left f (map k l) a = fold_left (fun a b => f a (k b)) l a.
Proof using.
Admitted.

Theorem fold_left_init : (forall (a : A) (b : B), h (f a b) = f (h a) b) -> forall (a : A) (l : list B), fold_left f l (h a) = h (fold_left f l a).
Proof using.
intros H a l; generalize a; elim l; clear l a; simpl in |- *; auto.
intros a l H0 a0.
Admitted.

Theorem lt_minus_O : forall n m, m < n -> 0 < n - m.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros m H1; contradict H1; auto with arith.
intros n1 Rec m; case m; simpl in |- *; auto.
intros m1 H1; apply Rec; apply lt_S_n; auto.

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

Theorem same_length_ex : forall (a : A) l1 l2 l3, length (l1 ++ a :: l2) = length l3 -> exists l4, (exists l5, (exists b : B, length l1 = length l4 /\ length l2 = length l5 /\ l3 = l4 ++ b :: l5)).
Proof using.
intros a l1; elim l1; simpl in |- *; auto.
intros l2 l3; case l3; simpl in |- *; try (intros; discriminate).
intros b l H; exists []; exists l; exists b; repeat (split; auto).
intros a0 l H l2 l3; case l3; simpl in |- *; try (intros; discriminate).
intros b l0 H0.
case (H l2 l0); auto.
intros l4 (l5, (b1, (HH1, (HH2, HH3)))).
exists (b :: l4); exists l5; exists b1; repeat (simpl in |- *; split; auto).
Admitted.

Theorem in_map_inv : forall (b : B) (l : list A), In b (map f l) -> exists a : A, In a l /\ b = f a.
Proof using.
intros b l; elim l; simpl in |- *; auto.
intros tmp; case tmp.
intros a0 l0 H [H1| H1]; auto.
exists a0; auto.
Admitted.

Theorem in_map_fst_inv : forall a (l : list (B * C)), In a (map (fst (B:=_)) l) -> exists c, In (a, c) l.
Proof using.
intros a l; elim l; simpl in |- *; auto.
intros H; case H.
intros a0 l0 H [H0| H0]; auto.
exists (snd a0); left; rewrite <- H0; case a0; simpl in |- *; auto.
Admitted.

Theorem in_flat_map_in : forall (l : list B) (f : B -> list C) a b, In a (f b) -> In b l -> In a (flat_map f l).
Proof using.
Admitted.

Theorem in_flat_map_ex : forall (l : list B) (f : B -> list C) a, In a (flat_map f l) -> exists b, In b l /\ In a (f b).
Proof using.
Admitted.

Theorem map2_app : forall l1 l2 l3 l4, length l1 = length l2 -> map2 (l1 ++ l3) (l2 ++ l4) = map2 l1 l2 ++ map2 l3 l4.
Proof using.
intros l1; elim l1; auto.
intros l2; case l2; simpl in |- *; auto; intros; discriminate.
intros a l H l2 l3 l4; case l2.
simpl in |- *; intros; discriminate.
intros b l0 H0.
apply trans_equal with (f a b :: map2 (l ++ l3) (l0 ++ l4)).
simpl in |- *; auto.
Admitted.

Theorem firstn_le_app1 : forall (n : nat) (l1 l2 : list A), length l1 <= n -> firstn n (l1 ++ l2) = l1 ++ firstn (n - length l1) l2.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros l1; case l1; simpl in |- *; auto.
intros b l l2 H; contradict H; auto with arith.
intros n0 H l1; case l1; simpl in |- *; auto with arith.
Admitted.

Theorem firstn_le_app2 : forall (n : nat) (l1 l2 : list A), n <= length l1 -> firstn n (l1 ++ l2) = firstn n l1.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros n0 H l1 l2; case l1; simpl in |- *.
intros H1; contradict H1; auto with arith.
intros a l H0; (apply f_equal2 with (f := cons (A:=A)); auto).
Admitted.

Theorem firstn_le_length_eq : forall (n : nat) (l1 : list A), n <= length l1 -> length (firstn n l1) = n.
Proof using.
intros n l1; generalize n; elim l1; clear n l1; simpl in |- *; auto.
intros n; case n; simpl in |- *; auto.
intros n1 H1; contradict H1; auto with arith.
Admitted.

Theorem skipn_le_app1 : forall (n : nat) (l1 l2 : list A), length l1 <= n -> skipn n (l1 ++ l2) = skipn (n - length l1) l2.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros l1; case l1; simpl in |- *; auto.
intros b l l2 H; contradict H; auto with arith.
Admitted.

Theorem length_skipn : forall (n : nat) (l1 : list A), length (skipn n l1) = length l1 - n.
Proof using.
intros n; elim n; simpl in |- *; auto with arith.
Admitted.

Theorem skipn_length_all : forall l : list A, skipn (length l) l = [].
Proof using.
Admitted.

Theorem exist_first_max : forall l : list nat, l <> [] -> exists a : nat, (exists l1 : list nat, (exists l2 : list nat, l = l1 ++ a :: l2 /\ (forall n1, In n1 l1 -> n1 < a) /\ (forall n1, In n1 l2 -> n1 <= a))).
Proof using.
intros l; elim l; simpl in |- *; auto.
intros H; case H; auto.
intros a l0; case l0.
intros H H0; exists a; exists []; exists []; repeat (split; simpl in |- *; auto with datatypes).
intros n1 H1; case H1.
intros n1 H1; case H1.
intros n l1 H H0; case H; clear H; auto.
red in |- *; intros H1; discriminate; auto.
intros a1 (l2, (l3, (HH1, (HH2, HH3)))).
case (le_or_lt a1 a); intros HH4; auto.
exists a; exists []; exists (n :: l1); repeat (split; auto with datatypes).
intros n1 H1; case H1.
rewrite HH1.
intros n1 H1; apply le_trans with (2 := HH4); case in_app_or with (1 := H1); auto with arith.
intros H2; apply lt_le_weak; auto.
simpl in |- *; intros [H2| H2]; [ rewrite H2 | idtac ]; auto.
exists a1; exists (a :: l2); exists l3; repeat (split; simpl in |- *; auto with datatypes).
apply f_equal2 with (f := cons (A:=nat)); auto.
Admitted.

Theorem find_min_correct : forall l : list A, match find_min l with | None => l = [] | Some (a, b) => (In b l /\ a = f b) /\ (forall c : A, In c l -> f b <= f c) end.
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a l0; case (find_min l0); simpl in |- *.
intros p; case p; simpl in |- *.
intros n b ((H1, H2), H3); case (le_lt_dec n (f a)); simpl in |- *.
intros H4; split; auto.
intros c [H5| H5]; auto.
rewrite <- H2; rewrite <- H5; auto.
intros H4; split; auto.
intros c [H5| H5]; auto.
rewrite <- H5; auto.
apply le_trans with (f b); auto.
rewrite <- H2; auto with arith.
intros H; rewrite H; split; simpl in |- *; auto.
Admitted.

Theorem find_max_correct : forall l : list A, match find_max l with | None => l = [] | Some (a, b) => (In b l /\ a = f b) /\ (forall c : A, In c l -> f c <= f b) end.
Proof using.
intros l; elim l; simpl in |- *; auto.
intros a l0; case (find_max l0); simpl in |- *.
intros p; case p; simpl in |- *.
intros n b ((H1, H2), H3); case (le_lt_dec n (f a)); simpl in |- *.
intros H4; split; auto.
intros c [H5| H5]; auto.
rewrite <- H5; auto.
apply le_trans with (f b); auto.
rewrite <- H2; auto with arith.
intros H4; split; auto.
intros c [H5| H5]; auto.
rewrite <- H5; auto.
apply le_trans with (f b); auto.
rewrite <- H2; auto with arith.
intros H; rewrite H; split; simpl in |- *; auto.
Admitted.

Theorem skipn_le_app2 : forall (n : nat) (l1 l2 : list A), n <= length l1 -> skipn n (l1 ++ l2) = skipn n l1 ++ l2.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros n0 H l1; case l1; simpl in |- *; auto with arith.
intros l2 H1; contradict H1; auto with arith.

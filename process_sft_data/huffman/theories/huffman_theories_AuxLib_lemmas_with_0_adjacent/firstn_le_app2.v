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

Theorem firstn_le_app2 : forall (n : nat) (l1 l2 : list A), n <= length l1 -> firstn n (l1 ++ l2) = firstn n l1.
Proof using.
intros n; elim n; simpl in |- *; auto.
intros n0 H l1 l2; case l1; simpl in |- *.
intros H1; contradict H1; auto with arith.
intros a l H0; (apply f_equal2 with (f := cons (A:=A)); auto).
apply H; apply le_S_n; auto.

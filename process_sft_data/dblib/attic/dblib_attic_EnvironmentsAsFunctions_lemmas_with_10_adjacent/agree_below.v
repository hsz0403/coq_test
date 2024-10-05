Set Implicit Arguments.
Require Import FunctionalExtensionality.
Require Import DblibTactics.
Require Import DeBruijn.
Require Import Lia.
Definition env A := nat -> option A.
Definition empty A : env A := fun y => None.
Definition lookup A (x : nat) (e : env A) : option A := e x.
Definition insert A (x : nat) (a : A) (e : env A) : env A := fun y => match lt_eq_lt_dec x y with | inleft (left _) (* x < y *) => e (y - 1) | inleft (right _) (* x = y *) => Some a | inright _ (* x > y *) => e y end.
Definition remove A (x : nat) (e : env A) : env A := fun y => match le_gt_dec x y with | left _ (* x <= y *) => e (1 + y) | right _ (* x > y *) => e y end.
Definition map A (f : A -> A) (e : env A) := fun y => match e y with | None => None | Some a => Some (f a) end.
Ltac one_plus_x_minus_one := repeat rewrite one_plus_x_minus_one_left; repeat rewrite one_plus_x_minus_one_right by lia.
Ltac lookup_insert := first [ rewrite lookup_insert_bingo by lia | rewrite lookup_insert_old by lia; one_plus_x_minus_one | rewrite lookup_insert_recent by lia | rewrite lookup_shift_insert ].
Ltac lookup_insert_all := first [ rewrite lookup_insert_bingo in * by lia | rewrite lookup_insert_old in * by lia; one_plus_x_minus_one | rewrite lookup_insert_recent in * by lia | rewrite lookup_shift_insert in * ].
Hint Extern 1 (lookup _ (insert _ _ _) = _) => lookup_insert : lookup_insert.
Hint Extern 1 (lookup _ _ = _) => lookup_insert_all : lookup_insert.
Ltac insert_insert := first [ rewrite insert_insert by lia; reflexivity | rewrite <- insert_insert by lia; reflexivity ].
Hint Extern 1 (insert _ _ (insert _ _ _) = _) => insert_insert : insert_insert.
Hint Extern 1 (_ = insert _ _ (insert _ _ _)) => insert_insert : insert_insert.
Ltac insert_remove := first [ rewrite insert_remove_recent by lia; reflexivity | rewrite insert_remove_old by lia; reflexivity | rewrite <- insert_remove_recent by lia; reflexivity | rewrite <- insert_remove_old by lia; reflexivity ].
Hint Extern 1 (remove _ (insert _ _ _) = insert _ _ (remove _ _)) => insert_remove : insert_remove.
Hint Extern 1 (insert _ _ (remove _ _)= remove _ (insert _ _ _) ) => insert_remove : insert_remove.
Ltac lookup_remove := first [ rewrite lookup_remove_old by lia; one_plus_x_minus_one | rewrite lookup_remove_recent by lia ].
Hint Extern 1 (lookup _ (remove _ _) = _) => lookup_remove : lookup_remove.
Ltac map_insert := first [ rewrite map_insert; reflexivity | rewrite <- map_insert; reflexivity ].
Hint Extern 1 (map _ (insert _ _ _) = insert _ _ (map _ _)) => map_insert : map_insert.
Hint Extern 1 (insert _ _ (map _ _) = map _ (insert _ _ _)) => map_insert : map_insert.
Definition length A (e : env A) (k : nat) := forall x, k <= x -> lookup x e = None.
Hint Resolve defined_implies_below_length : lift_idx_hints.
Hint Resolve length_empty length_insert : length.
Hint Resolve length_insert : construction_closed.
Definition agree A (e1 e2 : env A) (k : nat) := forall x, x < k -> lookup x e1 = lookup x e2.
Hint Resolve agree_below agree_empty agree_insert : agree.
Fixpoint concat (A : Type) (e1 : env A) (e2 : list A) : env A := match e2 with | nil => e1 | cons a e2 => concat (insert 0 a e1) e2 end.
Hint Resolve length_concat : length construction_closed.
Hint Resolve agree_concat : agree.
Fixpoint replicate (A : Type) (n : nat) (a : A) : list A := match n with | 0 => @nil _ | S n => cons a (replicate n a) end.
Hint Resolve insert_concat length_replicate insert_concat_replicate concat_replicate_is_iterated_insert : insert_concat.
Hint Resolve length_concat_replicate : length construction_closed.
Global Opaque empty lookup insert remove map.

Lemma lookup_remove_old: forall A x y (e : env A), y >= x -> lookup y (remove x e) = lookup (1 + y) e.
Proof.
intros.
unfold lookup, remove.
Admitted.

Lemma lookup_remove_recent: forall A x y (e : env A), y < x -> lookup y (remove x e) = lookup y e.
Proof.
intros.
unfold lookup, remove.
Admitted.

Lemma map_insert: forall A f x (a : A) e, map f (insert x a e) = insert x (f a) (map f e).
Proof.
unfold map, insert.
intros.
extensionality y.
Admitted.

Lemma map_map_fuse: forall A f g h e, (forall (d : A), f (g d) = h d) -> map f (map g e) = map h e.
Proof.
intros.
unfold map.
extensionality y.
Admitted.

Lemma map_map_exchange: forall A f1 f2 g1 g2 e, (forall (d : A), f1 (f2 d) = g1 (g2 d)) -> map f1 (map f2 e) = map g1 (map g2 e).
Proof.
intros.
unfold map.
extensionality y.
Admitted.

Lemma map_lift_map_lift: forall T k s wk ws (e : env T), forall `{Lift T}, @LiftLift T _ -> k <= s -> map (lift wk k) (map (lift ws s) e) = map (lift ws (wk + s)) (map (lift wk k) e).
Proof.
Admitted.

Lemma map_map_vanish: forall A f g (e : env A), (forall x, f (g x) = x) -> map f (map g e) = e.
Proof.
intros.
unfold map.
extensionality y.
Admitted.

Lemma defined_implies_below_length: forall A (e : env A) x k a, length e k -> lookup x e = Some a -> x < k.
Proof.
intros.
case (le_gt_dec k x); intro; try tauto.
assert (lookup x e = None).
auto.
Admitted.

Lemma length_empty: forall A k, length (@empty A) k.
Proof.
repeat intro.
Admitted.

Lemma length_insert: forall A (e : env A) k a, length e k -> length (insert 0 a e) (1 + k).
Proof.
unfold length; intros.
lookup_insert.
Admitted.

Lemma agree_empty: forall A (e : env A), agree (@empty _) e 0.
Proof.
unfold agree.
intros.
elimtype False.
Admitted.

Lemma agree_insert: forall A (e1 e2 : env A) k, agree e1 e2 k -> forall x a, x <= k -> agree (insert x a e1) (insert x a e2) (1 + k).
Proof.
unfold agree, lookup, insert.
intros.
Admitted.

Lemma length_concat: forall A (e2 : list A) (e1 : env A) n1 n, length e1 n1 -> n1 + List.length e2 = n -> length (concat e1 e2) n.
Proof.
induction e2; simpl; intros.
replace n with n1 by lia.
assumption.
Admitted.

Lemma agree_concat: forall A (e : list A) (e1 e2 : env A) k n, agree e1 e2 k -> k + List.length e = n -> agree (concat e1 e) (concat e2 e) n.
Proof.
induction e; simpl; intros.
replace n with k by lia.
assumption.
Admitted.

Lemma insert_concat: forall (A : Type) n x nx (a : A) e1 e2, List.length e2 = n -> n + x = nx -> insert nx a (concat e1 e2) = concat (insert x a e1) e2.
Proof.
induction n; intros; subst; destruct e2; simpl in *; try discriminate; auto.
rewrite insert_insert by lia.
erewrite <- (IHn (1 + x)) by first [ congruence | eauto ].
Admitted.

Lemma length_replicate: forall (A : Type) n (a : A), List.length (replicate n a) = n.
Proof.
Admitted.

Lemma insert_concat_replicate: forall (A : Type) n x nx (a b : A) e1, n + x = nx -> insert nx a (concat e1 (replicate n b)) = concat (insert x a e1) (replicate n b).
Proof.
Admitted.

Lemma concat_replicate_is_iterated_insert: forall (A : Type) n (a : A) e, insert n a (concat e (replicate n a)) = concat e (replicate (S n) a).
Proof.
intros.
simpl.
Admitted.

Lemma length_concat_replicate: forall A (a : A) (e1 : env A) n1 n2 n, length e1 n1 -> n1 + n2 = n -> length (concat e1 (replicate n2 a)) n.
Proof.
intros.
eapply length_concat.
eauto.
rewrite length_replicate.
Admitted.

Lemma agree_below: forall A (e1 e2 : env A) x a k, lookup x e1 = Some a -> length e1 k -> agree e1 e2 k -> lookup x e2 = Some a.
Proof.
do 6 intro.
intros hlookup ? ?.
rewrite <- hlookup.
symmetry.
eauto using defined_implies_below_length.

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

Lemma one_plus_x_minus_one_left: forall x, (1 + x) - 1 = x.
Proof.
intros.
Admitted.

Lemma one_plus_x_minus_one_right: forall x, x > 0 -> 1 + (x - 1) = x.
Proof.
intros.
Admitted.

Lemma lookup_empty_None: forall A x, lookup x (@empty A) = None.
Proof.
unfold lookup, empty.
Admitted.

Lemma lookup_insert_bingo: forall A x y (a : A) e, x = y -> lookup x (insert y a e) = Some a.
Proof.
intros.
subst.
unfold lookup, insert.
dblib_by_cases.
Admitted.

Lemma lookup_insert_recent: forall A x y (a : A) e, x < y -> lookup x (insert y a e) = lookup x e.
Proof.
intros.
unfold lookup, insert.
dblib_by_cases.
Admitted.

Lemma lookup_insert_old: forall A x y (a : A) e, x > y -> lookup x (insert y a e) = lookup (x - 1) e.
Proof.
intros.
unfold lookup, insert.
dblib_by_cases.
Admitted.

Lemma lookup_shift_insert: forall A x y (a : A) e, lookup (shift y x) (insert y a e) = lookup x e.
Proof.
intros.
destruct_lift_idx.
rewrite lookup_insert_old by lia.
f_equal.
lia.
rewrite lookup_insert_recent by lia.
Admitted.

Lemma lookup_map_some: forall A x (a : A) e f, lookup x e = Some a -> lookup x (map f e) = Some (f a).
Proof.
unfold lookup, map.
intros.
Admitted.

Lemma insert_insert: forall A k s (a b : A) e, k <= s -> insert k a (insert s b e) = insert (1 + s) b (insert k a e).
Proof.
unfold insert.
intros.
extensionality y.
Admitted.

Lemma remove_insert: forall A x (a : A) e, remove x (insert x a e) = e.
Proof.
intros.
unfold remove, insert.
extensionality y.
Admitted.

Lemma insert_remove_bingo: forall A x y (a : A) e, lookup x e = Some a -> y = x -> insert y a (remove x e) = e.
Proof.
unfold lookup, remove, insert.
intros.
extensionality z.
Admitted.

Lemma insert_remove_recent: forall A x y (a : A) e, y <= x -> insert y a (remove x e) = remove (1 + x) (insert y a e).
Proof.
intros.
unfold insert, remove.
extensionality z.
Admitted.

Lemma insert_remove_old: forall A x y (a : A) e, y >= x -> insert y a (remove x e) = remove x (insert (1 + y) a e).
Proof.
intros.
unfold insert, remove.
extensionality z.
Admitted.

Lemma lookup_empty_Some: forall A x (a : A), lookup x (@empty _) = Some a -> False.
Proof.
unfold lookup, empty.
intros.
congruence.

Set Implicit Arguments.
Require Import List.
Require Import Arith.
Require Import Lia.
Opaque plus.
From Dblib Require Import DblibTactics DeBruijn.
Definition env A := list (option A).
Definition empty A : env A := nil.
Fixpoint lookup A (x : nat) (e : env A) : option A := match e, x with | nil, _ => None | entry :: _, 0 => entry | _ :: e, S x => lookup x e end.
Fixpoint raw_insert A (x : nat) (o : option A) (e : env A) : env A := match x, e with | 0, _ => o :: e | S x, entry :: e => entry :: raw_insert x o e | S x, nil => None :: raw_insert x o e end.
Notation insert x a e := (raw_insert x (Some a) e).
Fixpoint map A B (f : A -> B) (e : env A) := match e with | nil => nil | None :: e => None :: map f e | Some a :: e => Some (f a) :: map f e end.
Fixpoint fold A B (f : option A -> B -> B) (e : env A) (accu : B) : B := match e with | nil => accu | o :: e => f o (fold f e accu) end.
Ltac one_plus_x_minus_one := repeat rewrite one_plus_x_minus_one_left in *; repeat rewrite one_plus_x_minus_one_right in * by lia.
Ltac lookup_insert := first [ rewrite lookup_insert_bingo by lia | rewrite lookup_insert_old by lia; one_plus_x_minus_one | rewrite lookup_insert_recent by lia | rewrite lookup_shift_insert ].
Ltac lookup_insert_all := first [ rewrite lookup_insert_bingo in * by lia; try match goal with h: Some _ = Some _ |- _ => injection h; intro; subst; clear h end | rewrite lookup_insert_old in * by lia; one_plus_x_minus_one | rewrite lookup_insert_recent in * by lia | rewrite lookup_shift_insert in * ].
Hint Extern 1 (lookup _ (raw_insert _ _ _) = _) => lookup_insert : lookup_insert.
Hint Extern 1 (lookup _ _ = _) => lookup_insert_all : lookup_insert.
Ltac insert_insert := first [ rewrite insert_insert; [ reflexivity | lia ] | rewrite <- insert_insert; [ reflexivity | lia ] ].
Hint Extern 1 (raw_insert _ _ _ = _) => insert_insert : insert_insert.
Hint Extern 1 (_ = raw_insert _ _ _) => insert_insert : insert_insert.
Ltac map_insert := first [ rewrite map_insert; reflexivity | rewrite <- map_insert; reflexivity ].
Hint Extern 1 (map _ (insert _ _ _) = insert _ _ (map _ _)) => map_insert : map_insert.
Hint Extern 1 (insert _ _ (map _ _) = map _ (insert _ _ _)) => map_insert : map_insert.
Hint Resolve defined_implies_below_length : lift_idx_hints.
Definition mymax m n := if le_gt_dec m n then n else m.
Ltac mymax := unfold mymax in *; dblib_by_cases; try lia.
Hint Resolve mymax_l mymax_r : mymax.
Hint Resolve length_empty length_insert length_map : length.
Hint Resolve length_insert length_map : construction_closed.
Opaque empty lookup raw_insert map.
Definition agree A (e1 e2 : env A) (k : nat) := forall x, x < k -> lookup x e1 = lookup x e2.
Hint Resolve defined_implies_below_length agree_below agree_empty_left agree_empty_right agree_insert : agree.
Section Subsume.
Variable A : Type.
Variable sub : A -> A -> Prop.
Variable sub_reflexive: forall a, sub a a.
Variable sub_transitive: forall a1 a2 a3, sub a1 a2 -> sub a2 a3 -> sub a1 a3.
Definition osub (o1 o2 : option A) := forall a2, o2 = Some a2 -> exists a1, o1 = Some a1 /\ sub a1 a2.
Definition subsume (e1 e2 : env A) := forall x, osub (lookup x e1) (lookup x e2).
End Subsume.
Hint Resolve osub_reflexive osub_Some_Some subsume_reflexive subsume_transitive subsume_empty subsume_insert subsume_map : subsume.
Fixpoint concat (A : Type) (e1 : env A) (e2 : list A) : env A := match e2 with | nil => e1 | cons a e2 => concat (insert 0 a e1) e2 end.
Hint Resolve length_concat : length construction_closed.
Hint Resolve agree_concat : agree.
Fixpoint replicate (A : Type) (n : nat) (a : A) : list A := match n with | 0 => @nil _ | S n => cons a (replicate n a) end.
Hint Resolve insert_concat length_replicate insert_concat_replicate concat_replicate_is_iterated_insert : insert_concat.
Hint Resolve length_concat_replicate : length construction_closed.
Global Opaque empty lookup raw_insert map.

Lemma one_plus_x_minus_one_right: forall x, x > 0 -> 1 + (x - 1) = x.
Proof.
intros.
Admitted.

Lemma raw_insert_zero: forall A o (e : env A), raw_insert 0 o e = o :: e.
Proof.
Admitted.

Lemma raw_insert_successor: forall A x o (e : env A), raw_insert (S x) o e = lookup 0 e :: raw_insert x o (tail e).
Proof.
intros.
Admitted.

Lemma empty_eq_insert: forall A x o (e : env A), empty _ = insert x o e -> False.
Proof.
unfold empty; intros; destruct x.
-
rewrite raw_insert_zero in *.
congruence.
-
rewrite raw_insert_successor in *.
Admitted.

Lemma lookup_empty_None: forall A x, lookup x (@empty A) = None.
Proof.
Admitted.

Lemma lookup_empty_Some: forall A x (a : A), lookup x (@empty _) = Some a -> False.
Proof.
Admitted.

Lemma lookup_successor: forall A x (e : env A), lookup (S x) e = lookup x (tail e).
Proof.
destruct e.
-
do 2 rewrite lookup_empty_None.
reflexivity.
-
Admitted.

Lemma lookup_insert_bingo: forall A x y (o : option A) e, x = y -> lookup x (raw_insert y o e) = o.
Proof.
Admitted.

Lemma lookup_insert_recent: forall A x y (o : option A) e, x < y -> lookup x (raw_insert y o e) = lookup x e.
Proof.
induction x; intros; destruct y; destruct e; simpl; intuition; try lia.
-
erewrite <- lookup_empty_None.
Admitted.

Lemma lookup_insert_old: forall A x y (o : option A) e, x > y -> lookup x (raw_insert y o e) = lookup (x - 1) e.
Proof.
induction x; intros; [ elimtype False; lia | replace (S x - 1) with x by lia ].
-
{
destruct y; destruct e; simpl; try solve [ eauto ].
-
rewrite lookup_empty_None.
erewrite <- lookup_empty_None.
intuition.
-
destruct x; intros; [ elimtype False; lia | replace (S x - 1) with x in * by lia ].
simpl lookup at 2.
intuition.
Admitted.

Lemma lookup_shift_insert: forall A x y (o : option A) e, lookup (shift y x) (raw_insert y o e) = lookup x e.
Proof.
intros.
destruct_lift_idx.
-
rewrite lookup_insert_old by lia.
f_equal.
lia.
-
rewrite lookup_insert_recent by lia.
Admitted.

Lemma map_empty: forall A B (f : A -> B), map f (@empty _) = @empty _.
Proof.
Admitted.

Lemma lookup_map_none: forall A B x e (f : A -> B), lookup x e = None -> lookup x (map f e) = None.
Proof.
Admitted.

Lemma lookup_map_some: forall A B x a e (f : A -> B), lookup x e = Some a -> lookup x (map f e) = Some (f a).
Proof.
Admitted.

Lemma lookup_map_some_reverse: forall A B x b e (f : A -> B), lookup x (map f e) = Some b -> exists a, lookup x e = Some a /\ b = f a.
Proof.
induction x; intros; destruct e as [ | [ | ] ? ]; simpl in *; subst; try solve [ congruence | eauto ].
-
eexists.
split.
reflexivity.
Admitted.

Lemma insert_insert: forall A k s (a b : option A) e, k <= s -> raw_insert k a (raw_insert s b e) = raw_insert (1 + s) b (raw_insert k a e).
Proof.
intros ? k s.
generalize s k; clear s k.
induction s; intros.
-
destruct k; [ | elimtype False; lia ].
reflexivity.
-
{
destruct k.
-
reflexivity.
-
destruct e; replace (1 + S s) with (S (1 + s)) by lia; simpl; f_equal; intuition.
Admitted.

Lemma insert_insert_always: forall A k s (a b : option A) e, raw_insert k a (raw_insert s b e) = raw_insert (shift k s) b (raw_insert (if le_gt_dec k s then k else k - 1) a e).
Proof.
intros.
destruct (le_gt_dec k s).
-
rewrite lift_idx_old by assumption.
eauto using insert_insert.
-
rewrite lift_idx_recent by assumption.
replace k with (1 + (k - 1)) in * by lia.
rewrite <- insert_insert by lia.
do 2 f_equal.
Admitted.

Lemma insert_nil: forall A x a (e : env A), insert x a e = nil -> False.
Proof.
Admitted.

Lemma insert_eq_insert_1: forall A x a1 a2 (e1 e2 : env A), insert x a1 e1 = insert x a2 e2 -> a1 = a2.
Proof.
intros.
assert (lookup x (insert x a1 e1) = Some a1).
eauto using lookup_insert_bingo.
assert (lookup x (insert x a2 e2) = Some a2).
eauto using lookup_insert_bingo.
Admitted.

Lemma insert_eq_insert_2: forall A x a1 a2 (e1 e2 : env A), insert x a1 e1 = insert x a2 e2 -> forall b, insert x b e1 = insert x b e2.
Proof.
induction x; simpl; intros.
-
congruence.
-
Admitted.

Lemma one_plus_x_minus_one_left: forall x, (1 + x) - 1 = x.
Proof.
intros.
lia.

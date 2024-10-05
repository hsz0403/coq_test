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

Lemma map_lift_map_lift: forall T k s wk ws (e : env T), forall `{Lift T}, @LiftLift T _ -> k <= s -> map (lift wk k) (map (lift ws s) e) = map (lift ws (wk + s)) (map (lift wk k) e).
Proof.
Admitted.

Lemma map_insert_map: forall A (f g h : A -> A) x (a : A) e, (forall a, f (g a) = g (h a)) -> map f (insert x a (map g e)) = insert x (f a) (map g (map h e)).
Proof.
intros.
rewrite map_insert.
f_equal.
eapply map_map_exchange.
Admitted.

Lemma map_map_vanish: forall A B (f : B -> A) (g : A -> B) (e : env A), (forall x, f (g x) = x) -> map f (map g e) = e.
Proof.
Admitted.

Lemma fold_empty: forall A B (f : option A -> B -> B) accu, fold f (@empty _) accu = accu.
Proof.
Admitted.

Lemma fold_insert: forall A B (f : option A -> B -> B) o e accu, fold f (raw_insert 0 o e) accu = f o (fold f e accu).
Proof.
Admitted.

Lemma fold_invariant: forall A B (P : env A -> B -> Prop) f accu, P (@empty _) accu -> (forall o e accu, P e accu -> P (raw_insert 0 o e) (f o accu)) -> forall e, P e (fold f e accu).
Proof.
intros ? ? ? ? ? init step.
induction e; simpl.
-
eapply init.
-
eapply step.
Admitted.

Lemma length_monotonic: forall A (e : env A) k1 k2, length e <= k1 -> k1 <= k2 -> length e <= k2.
Proof.
intros.
Admitted.

Lemma lookup_beyond_length: forall A (e : env A) x, length e <= x -> lookup x e = None.
Proof.
induction e; simpl; intros.
-
eapply lookup_empty_None.
-
destruct x; [ lia | ].
simpl.
eapply IHe.
Admitted.

Lemma defined_implies_below_length: forall A (e : env A) x k a, length e <= k -> lookup x e = Some a -> x < k.
Proof.
intros.
{
case (le_gt_dec k x); intro; try tauto.
-
assert (lookup x e = None).
eapply lookup_beyond_length.
lia.
congruence.
Admitted.

Lemma length_empty: forall A k, length (@empty A) <= k.
Proof.
simpl.
intros.
Admitted.

Lemma mymax_r: forall i j, mymax i j >= j.
Proof.
intros.
Admitted.

Lemma length_insert_general: forall A x k o (e : env A), length e = k -> length (raw_insert x o e) = mymax (1 + k) (1 + x).
Proof.
induction x; simpl; intros; subst.
-
mymax.
-
{
destruct e; simpl.
-
mymax.
erewrite IHx by reflexivity.
simpl.
mymax.
-
erewrite IHx by reflexivity.
mymax.
Admitted.

Lemma length_insert: forall A x k km1 o (e : env A), length e <= km1 -> km1 <= k - 1 -> x < k -> length (raw_insert x o e) <= k.
Proof.
intros.
erewrite length_insert_general by reflexivity.
Admitted.

Lemma length_insert_reverse_1: forall A (e : env A) k x a, length (insert x a e) <= k -> x < k.
Proof.
intros.
erewrite length_insert_general in * by reflexivity.
Admitted.

Lemma length_insert_reverse_2: forall A (e : env A) k x a, length (insert x a e) <= k + 1 -> length e <= k.
Proof.
intros.
erewrite length_insert_general in * by reflexivity.
Admitted.

Lemma length_insert_independent: forall A (e : env A) k x a, length (insert x a e) <= k -> forall y o, y < k -> length (raw_insert y o e) <= k.
Proof.
intros.
erewrite length_insert_general in * by reflexivity.
Admitted.

Lemma length_map_general: forall A B (f : A -> B) (e : env A), length (map f e) = length e.
Proof.
Admitted.

Lemma length_map: forall A B (f : A -> B) (e : env A) k, length e <= k -> length (map f e) <= k.
Proof.
intros.
rewrite length_map_general.
Admitted.

Lemma agree_below: forall A (e1 e2 : env A) x a k, lookup x e1 = Some a -> x < k -> agree e1 e2 k -> lookup x e2 = Some a.
Proof.
do 6 intro.
intros hlookup ? ?.
rewrite <- hlookup.
symmetry.
Admitted.

Lemma agree_empty_left: forall A (e : env A), agree (@empty _) e 0.
Proof.
unfold agree.
intros.
elimtype False.
Admitted.

Lemma mymax_l: forall i j, mymax i j >= i.
Proof.
intros.
mymax.

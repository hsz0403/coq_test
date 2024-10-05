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

Lemma insert_eq_insert_3: forall A x1 x2 a1 a2 (e1 e2 : env A), insert x1 a1 e1 = insert x2 a2 e2 -> x1 <> x2 -> exists e y1 y2, e1 = insert y1 a2 e /\ e2 = insert y2 a1 e /\ shift x1 y1 = x2 /\ y2 = (if le_gt_dec x1 y1 then x1 else x1 - 1).
Proof.
induction x1; intros.
-
{
destruct x2; [ lia | ].
-
rewrite raw_insert_zero in *.
rewrite raw_insert_successor in *.
match goal with h: _ = _ |- _ => injection h; clear h; intros end.
{
destruct e2; [ congruence | ].
-
subst.
simpl.
exists e2.
exists x2.
exists 0.
eauto.
}
}
-
{
destruct x2.
-
rewrite raw_insert_zero in *.
rewrite raw_insert_successor in *.
match goal with h: _ = _ |- _ => injection h; clear h; intros end.
{
destruct e1; [ congruence | ].
subst.
-
exists e1.
exists 0.
exists x1.
split.
eauto.
split.
eauto.
split.
eauto.
dblib_by_cases.
lia.
}
-
do 2 rewrite raw_insert_successor in *.
assert (xx: x1 <> x2).
lia.
match goal with h: _ = _ |- _ => injection h; clear h; intros h ?; generalize (IHx1 _ _ _ _ _ h xx); intros [ e [ y1 [ y2 [ ? [ ? [ ? ? ]]]]]] end.
{
destruct e1; simpl tl in *; [ elimtype False; eauto using insert_nil | ].
-
destruct e2; simpl tl in *; [ elimtype False; eauto using insert_nil | ].
+
exists (o :: e).
exists (S y1).
exists (S y2).
split.
simpl.
congruence.
split.
simpl.
congruence.
split.
eapply translate_lift with (k := 1).
eauto.
dblib_by_cases; lia.
}
Admitted.

Lemma map_insert: forall A B (f : A -> B) x a e, map f (insert x a e) = insert x (f a) (map f e).
Proof.
induction x; intros; destruct e; simpl; eauto.
-
rewrite IHx.
reflexivity.
-
Admitted.

Lemma map_insert_eq: forall A B (f : A -> B) x a b e, f a = b -> map f (insert x a e) = insert x b (map f e).
Proof.
intros; subst.
Admitted.

Lemma map_raw_insert: forall A B (f : A -> B) x e, map f (raw_insert x None e) = raw_insert x None (map f e).
Proof.
induction x; intros; destruct e; simpl; eauto.
-
rewrite IHx.
reflexivity.
-
Admitted.

Lemma map_map_fuse: forall A B C (f : B -> C) (g : A -> B) h e, (forall (d : A), f (g d) = h d) -> map f (map g e) = map h e.
Proof.
Admitted.

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

Lemma map_map_exchange: forall A F G B (f1 : F -> B) (f2 : A -> F) (g1 : G -> B) (g2 : A -> G) e, (forall (d : A), f1 (f2 d) = g1 (g2 d)) -> map f1 (map f2 e) = map g1 (map g2 e).
Proof.
induction e; intros; try match goal with o: option _ |- _ => destruct o end; simpl; eauto with f_equal.

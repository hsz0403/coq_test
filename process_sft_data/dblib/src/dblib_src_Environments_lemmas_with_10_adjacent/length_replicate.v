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

Lemma subsume_insert: forall e1 e2, subsume e1 e2 -> forall x o1 o2, osub o1 o2 -> subsume (raw_insert x o1 e1) (raw_insert x o2 e2).
Proof.
unfold subsume.
do 7 intro.
intros n.
Admitted.

Lemma subsume_cons: forall o e1 e2, osub o (lookup 0 e2) -> subsume e1 (tl e2) -> subsume (o :: e1) e2.
Proof.
do 3 intro.
intros h1 h2.
intro n.
destruct n.
-
eauto.
-
do 2 rewrite lookup_successor.
Admitted.

Lemma subsume_cons_cons_inversion: forall o1 o2 e1 e2, subsume (o1 :: e1) (o2 :: e2) -> osub o1 o2 /\ subsume e1 e2.
Proof.
do 4 intro.
intro h.
split.
-
eapply (h 0).
-
intro n.
Admitted.

Lemma subsume_insert_inversion: forall e1 x a2 e2, subsume e1 (insert x a2 e2) -> exists f1 a1, e1 = insert x a1 f1 /\ subsume f1 e2 /\ sub a1 a2.
Proof.
induction e1; simpl; intros.
-
elimtype False.
match goal with h: subsume nil _ |- _ => generalize (h x); clear h; intro h; rewrite lookup_insert_bingo in h by reflexivity; rewrite lookup_empty_None in h end.
solve [ eauto using osub_None_Some ].
-
{
destruct x.
-
match goal with h: subsume _ _ |- _ => rewrite raw_insert_zero in h; generalize (subsume_cons_cons_inversion h); clear h; intros [ h ? ]; generalize (osub_Some_inversion h); intros [ ? [ ? ? ]]; subst end.
do 2 eexists.
rewrite raw_insert_zero.
solve [ eauto ].
-
match goal with h: subsume _ _ |- _ => rewrite raw_insert_successor in h; generalize (subsume_cons_cons_inversion h); clear h; intros [ ? h ]; generalize (IHe1 _ _ _ h); clear IHe1; intros [ f1 [ a1 [ ? [ ? ? ]]]]; subst end.
exists (a :: f1).
exists a1.
rewrite raw_insert_successor.
simpl.
split; [ | split ].
reflexivity.
eauto using subsume_cons.
eauto.
Admitted.

Lemma subsume_map: forall f, (forall a1 a2, sub a1 a2 -> sub (f a1) (f a2)) -> forall e1 e2, subsume e1 e2 -> subsume (map f e1) (map f e2).
Proof.
intros ? hf ? ? hs.
intros ? b2 hlm2.
generalize (lookup_map_some_reverse _ _ _ hlm2); intros [ ? [ hl2 ? ]].
subst.
generalize (hs _ _ hl2); intros [ a1 [ ? ? ]].
Admitted.

Lemma lia_hint_1: forall n, n <= (n + 1) - 1.
Proof.
intros.
Admitted.

Lemma length_concat: forall A (e2 : list A) (e1 : env A) n1 n, length e1 <= n1 -> n1 + length e2 = n -> length (concat e1 e2) <= n.
Proof.
induction e2; simpl; intros.
-
replace n with n1 by lia.
assumption.
-
Admitted.

Lemma agree_concat: forall A (e : list A) (e1 e2 : env A) k n, agree e1 e2 k -> k + length e = n -> agree (concat e1 e) (concat e2 e) n.
Proof.
induction e; simpl; intros.
-
replace n with k by lia.
assumption.
-
Admitted.

Lemma insert_concat: forall (A : Type) n x nx (o : option A) e1 e2, length e2 = n -> n + x = nx -> raw_insert nx o (concat e1 e2) = concat (raw_insert x o e1) e2.
Proof.
induction n; intros; subst; destruct e2; simpl in *; try discriminate; auto.
-
rewrite insert_insert by lia.
erewrite <- (IHn (1 + x)) by first [ congruence | eauto ].
Admitted.

Lemma concat_app: forall (A : Type) e1 (e2 e3 : list A), concat e1 (e2 ++ e3) = concat (concat e1 e2) e3.
Proof.
intros A e1 e2 e3.
generalize e1.
clear e1.
Admitted.

Lemma insert_concat_replicate: forall (A : Type) n x nx (a : option A) (b : A) e1, n + x = nx -> raw_insert nx a (concat e1 (replicate n b)) = concat (raw_insert x a e1) (replicate n b).
Proof.
Admitted.

Lemma concat_replicate_is_iterated_insert: forall (A : Type) n (a : A) e, insert n a (concat e (replicate n a)) = concat e (replicate (S n) a).
Proof.
intros.
simpl.
Admitted.

Lemma length_concat_replicate: forall A (a : A) (e1 : env A) n1 n2 n, length e1 <= n1 -> n1 + n2 = n -> length (concat e1 (replicate n2 a)) <= n.
Proof.
intros.
eapply length_concat.
eauto.
rewrite length_replicate.
Admitted.

Lemma length_replicate: forall (A : Type) n (a : A), length (replicate n a) = n.
Proof.
induction n; simpl; auto.

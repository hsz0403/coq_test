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
Lemma one_plus_x_minus_one_left: forall x, (1 + x) - 1 = x.
Proof.
intros.
lia.
Qed.
Lemma one_plus_x_minus_one_right: forall x, x > 0 -> 1 + (x - 1) = x.
Proof.
intros.
lia.
Qed.
Ltac one_plus_x_minus_one := repeat rewrite one_plus_x_minus_one_left in *; repeat rewrite one_plus_x_minus_one_right in * by lia.
Lemma raw_insert_zero: forall A o (e : env A), raw_insert 0 o e = o :: e.
Proof.
reflexivity.
Qed.
Lemma raw_insert_successor: forall A x o (e : env A), raw_insert (S x) o e = lookup 0 e :: raw_insert x o (tail e).
Proof.
intros.
destruct e; reflexivity.
Qed.
Lemma empty_eq_insert: forall A x o (e : env A), empty _ = insert x o e -> False.
Proof.
unfold empty; intros; destruct x.
-
rewrite raw_insert_zero in *.
congruence.
-
rewrite raw_insert_successor in *.
congruence.
Qed.
Lemma lookup_empty_None: forall A x, lookup x (@empty A) = None.
Proof.
destruct x; simpl; reflexivity.
Qed.
Lemma lookup_empty_Some: forall A x (a : A), lookup x (@empty _) = Some a -> False.
Proof.
destruct x; simpl; congruence.
Qed.
Lemma lookup_successor: forall A x (e : env A), lookup (S x) e = lookup x (tail e).
Proof.
destruct e.
-
do 2 rewrite lookup_empty_None.
reflexivity.
-
reflexivity.
Qed.
Lemma lookup_insert_bingo: forall A x y (o : option A) e, x = y -> lookup x (raw_insert y o e) = o.
Proof.
induction x; intros; destruct y; destruct e; simpl; intuition; lia.
Qed.
Lemma lookup_insert_recent: forall A x y (o : option A) e, x < y -> lookup x (raw_insert y o e) = lookup x e.
Proof.
induction x; intros; destruct y; destruct e; simpl; intuition; try lia.
-
erewrite <- lookup_empty_None.
intuition.
Qed.
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
}
Qed.
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
reflexivity.
Qed.
Ltac lookup_insert := first [ rewrite lookup_insert_bingo by lia | rewrite lookup_insert_old by lia; one_plus_x_minus_one | rewrite lookup_insert_recent by lia | rewrite lookup_shift_insert ].
Ltac lookup_insert_all := first [ rewrite lookup_insert_bingo in * by lia; try match goal with h: Some _ = Some _ |- _ => injection h; intro; subst; clear h end | rewrite lookup_insert_old in * by lia; one_plus_x_minus_one | rewrite lookup_insert_recent in * by lia | rewrite lookup_shift_insert in * ].
Hint Extern 1 (lookup _ (raw_insert _ _ _) = _) => lookup_insert : lookup_insert.
Hint Extern 1 (lookup _ _ = _) => lookup_insert_all : lookup_insert.
Lemma map_empty: forall A B (f : A -> B), map f (@empty _) = @empty _.
Proof.
reflexivity.
Qed.
Lemma lookup_map_none: forall A B x e (f : A -> B), lookup x e = None -> lookup x (map f e) = None.
Proof.
induction x; intros; destruct e as [ | [ | ] ? ]; simpl in *; subst; solve [ eauto | congruence ].
Qed.
Lemma lookup_map_some: forall A B x a e (f : A -> B), lookup x e = Some a -> lookup x (map f e) = Some (f a).
Proof.
induction x; intros; destruct e as [ | [ | ] ? ]; simpl in *; subst; try solve [ congruence | eauto ].
Qed.
Lemma lookup_map_some_reverse: forall A B x b e (f : A -> B), lookup x (map f e) = Some b -> exists a, lookup x e = Some a /\ b = f a.
Proof.
induction x; intros; destruct e as [ | [ | ] ? ]; simpl in *; subst; try solve [ congruence | eauto ].
-
eexists.
split.
reflexivity.
congruence.
Qed.
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
}
Qed.
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
lia.
Qed.
Ltac insert_insert := first [ rewrite insert_insert; [ reflexivity | lia ] | rewrite <- insert_insert; [ reflexivity | lia ] ].
Hint Extern 1 (raw_insert _ _ _ = _) => insert_insert : insert_insert.
Hint Extern 1 (_ = raw_insert _ _ _) => insert_insert : insert_insert.
Lemma insert_nil: forall A x a (e : env A), insert x a e = nil -> False.
Proof.
destruct x; destruct e; simpl; congruence.
Qed.
Lemma insert_eq_insert_1: forall A x a1 a2 (e1 e2 : env A), insert x a1 e1 = insert x a2 e2 -> a1 = a2.
Proof.
intros.
assert (lookup x (insert x a1 e1) = Some a1).
eauto using lookup_insert_bingo.
assert (lookup x (insert x a2 e2) = Some a2).
eauto using lookup_insert_bingo.
congruence.
Qed.
Lemma insert_eq_insert_2: forall A x a1 a2 (e1 e2 : env A), insert x a1 e1 = insert x a2 e2 -> forall b, insert x b e1 = insert x b e2.
Proof.
induction x; simpl; intros.
-
congruence.
-
destruct e1; destruct e2; match goal with h: _ = _ |- _ => injection h; clear h; intros end; f_equal; try congruence; eauto.
Qed.
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
}
Qed.
Lemma map_insert: forall A B (f : A -> B) x a e, map f (insert x a e) = insert x (f a) (map f e).
Proof.
induction x; intros; destruct e; simpl; eauto.
-
rewrite IHx.
reflexivity.
-
match goal with o: option _ |- _ => destruct o end; f_equal; eauto.
Qed.
Lemma map_insert_eq: forall A B (f : A -> B) x a b e, f a = b -> map f (insert x a e) = insert x b (map f e).
Proof.
intros; subst.
eapply map_insert.
Qed.
Ltac map_insert := first [ rewrite map_insert; reflexivity | rewrite <- map_insert; reflexivity ].
Hint Extern 1 (map _ (insert _ _ _) = insert _ _ (map _ _)) => map_insert : map_insert.
Hint Extern 1 (insert _ _ (map _ _) = map _ (insert _ _ _)) => map_insert : map_insert.
Lemma map_raw_insert: forall A B (f : A -> B) x e, map f (raw_insert x None e) = raw_insert x None (map f e).
Proof.
induction x; intros; destruct e; simpl; eauto.
-
rewrite IHx.
reflexivity.
-
match goal with o: option _ |- _ => destruct o end; f_equal; eauto.
Qed.
Lemma map_map_fuse: forall A B C (f : B -> C) (g : A -> B) h e, (forall (d : A), f (g d) = h d) -> map f (map g e) = map h e.
Proof.
induction e; intros; try match goal with o: option _ |- _ => destruct o end; simpl; eauto with f_equal.
Qed.
Lemma map_map_exchange: forall A F G B (f1 : F -> B) (f2 : A -> F) (g1 : G -> B) (g2 : A -> G) e, (forall (d : A), f1 (f2 d) = g1 (g2 d)) -> map f1 (map f2 e) = map g1 (map g2 e).
Proof.
induction e; intros; try match goal with o: option _ |- _ => destruct o end; simpl; eauto with f_equal.
Qed.
Lemma map_lift_map_lift: forall T k s wk ws (e : env T), forall `{Lift T}, @LiftLift T _ -> k <= s -> map (lift wk k) (map (lift ws s) e) = map (lift ws (wk + s)) (map (lift wk k) e).
Proof.
eauto using map_map_exchange, @lift_lift.
Qed.
Lemma map_insert_map: forall A (f g h : A -> A) x (a : A) e, (forall a, f (g a) = g (h a)) -> map f (insert x a (map g e)) = insert x (f a) (map g (map h e)).
Proof.
intros.
rewrite map_insert.
f_equal.
eapply map_map_exchange.
eauto.
Qed.
Lemma map_map_vanish: forall A B (f : B -> A) (g : A -> B) (e : env A), (forall x, f (g x) = x) -> map f (map g e) = e.
Proof.
induction e; intros; try match goal with o: option _ |- _ => destruct o end; simpl; eauto with f_equal.
Qed.
Lemma fold_empty: forall A B (f : option A -> B -> B) accu, fold f (@empty _) accu = accu.
Proof.
reflexivity.
Qed.
Lemma fold_insert: forall A B (f : option A -> B -> B) o e accu, fold f (raw_insert 0 o e) accu = f o (fold f e accu).
Proof.
reflexivity.
Qed.
Lemma fold_invariant: forall A B (P : env A -> B -> Prop) f accu, P (@empty _) accu -> (forall o e accu, P e accu -> P (raw_insert 0 o e) (f o accu)) -> forall e, P e (fold f e accu).
Proof.
intros ? ? ? ? ? init step.
induction e; simpl.
-
eapply init.
-
eapply step.
eauto.
Qed.
Lemma length_monotonic: forall A (e : env A) k1 k2, length e <= k1 -> k1 <= k2 -> length e <= k2.
Proof.
intros.
lia.
Qed.
Lemma lookup_beyond_length: forall A (e : env A) x, length e <= x -> lookup x e = None.
Proof.
induction e; simpl; intros.
-
eapply lookup_empty_None.
-
destruct x; [ lia | ].
simpl.
eapply IHe.
lia.
Qed.
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
}
Qed.
Hint Resolve defined_implies_below_length : lift_idx_hints.
Lemma length_empty: forall A k, length (@empty A) <= k.
Proof.
simpl.
intros.
lia.
Qed.
Definition mymax m n := if le_gt_dec m n then n else m.
Ltac mymax := unfold mymax in *; dblib_by_cases; try lia.
Lemma mymax_l: forall i j, mymax i j >= i.
Proof.
intros.
mymax.
Qed.
Lemma mymax_r: forall i j, mymax i j >= j.
Proof.
intros.
mymax.
Qed.
Hint Resolve mymax_l mymax_r : mymax.
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
}
Qed.
Lemma length_insert: forall A x k km1 o (e : env A), length e <= km1 -> km1 <= k - 1 -> x < k -> length (raw_insert x o e) <= k.
Proof.
intros.
erewrite length_insert_general by reflexivity.
mymax.
Qed.
Lemma length_insert_reverse_1: forall A (e : env A) k x a, length (insert x a e) <= k -> x < k.
Proof.
intros.
erewrite length_insert_general in * by reflexivity.
mymax.
Qed.
Lemma length_insert_reverse_2: forall A (e : env A) k x a, length (insert x a e) <= k + 1 -> length e <= k.
Proof.
intros.
erewrite length_insert_general in * by reflexivity.
mymax.
Qed.
Lemma length_insert_independent: forall A (e : env A) k x a, length (insert x a e) <= k -> forall y o, y < k -> length (raw_insert y o e) <= k.
Proof.
intros.
erewrite length_insert_general in * by reflexivity.
mymax.
Qed.
Lemma length_map_general: forall A B (f : A -> B) (e : env A), length (map f e) = length e.
Proof.
induction e as [| [|] ]; simpl; intros; congruence.
Qed.
Lemma length_map: forall A B (f : A -> B) (e : env A) k, length e <= k -> length (map f e) <= k.
Proof.
intros.
rewrite length_map_general.
assumption.
Qed.
Hint Resolve length_empty length_insert length_map : length.
Hint Resolve length_insert length_map : construction_closed.
Opaque empty lookup raw_insert map.
Definition agree A (e1 e2 : env A) (k : nat) := forall x, x < k -> lookup x e1 = lookup x e2.
Lemma agree_below: forall A (e1 e2 : env A) x a k, lookup x e1 = Some a -> x < k -> agree e1 e2 k -> lookup x e2 = Some a.
Proof.
do 6 intro.
intros hlookup ? ?.
rewrite <- hlookup.
symmetry.
eauto.
Qed.
Lemma agree_empty_left: forall A (e : env A), agree (@empty _) e 0.
Proof.
unfold agree.
intros.
elimtype False.
lia.
Qed.
Lemma agree_empty_right: forall A (e : env A), agree e (@empty _) 0.
Proof.
unfold agree.
intros.
elimtype False.
lia.
Qed.
Lemma agree_insert: forall A (e1 e2 : env A) k, agree e1 e2 k -> forall x o, x <= k -> agree (raw_insert x o e1) (raw_insert x o e2) (1 + k).
Proof.
unfold agree.
intros * H * ? n **.
destruct (lt_eq_lt_dec x n) as [[] | ]; intros; (* In each case, [lookup_insert] simplifies the goal. *) do 2 lookup_insert; (apply H; lia) || reflexivity.
Qed.
Hint Resolve defined_implies_below_length agree_below agree_empty_left agree_empty_right agree_insert : agree.
Section Subsume.
Variable A : Type.
Variable sub : A -> A -> Prop.
Variable sub_reflexive: forall a, sub a a.
Variable sub_transitive: forall a1 a2 a3, sub a1 a2 -> sub a2 a3 -> sub a1 a3.
Definition osub (o1 o2 : option A) := forall a2, o2 = Some a2 -> exists a1, o1 = Some a1 /\ sub a1 a2.
Lemma osub_None: forall o, osub o None.
Proof.
unfold osub.
congruence.
Qed.
Lemma osub_Some_Some: forall a1 a2, sub a1 a2 -> osub (Some a1) (Some a2).
Proof.
unfold osub.
intros ? ? ? ? h.
injection h; clear h; intro; subst; eauto.
Qed.
Lemma osub_None_Some: forall a2, osub None (Some a2) -> False.
Proof.
unfold osub.
intros ? h.
generalize (h _ eq_refl).
clear h.
intros [ a1 [ ? ? ]].
congruence.
Qed.
Lemma osub_Some_inversion: forall o1 a2, osub o1 (Some a2) -> exists a1, o1 = Some a1 /\ sub a1 a2.
Proof.
intros.
destruct o1.
-
eauto.
-
elimtype False.
eauto using osub_None_Some.
Qed.
Definition subsume (e1 e2 : env A) := forall x, osub (lookup x e1) (lookup x e2).
Lemma osub_reflexive: forall o, osub o o.
Proof.
unfold osub.
eauto.
Qed.
Lemma subsume_reflexive: forall e, subsume e e.
Proof.
unfold subsume.
eauto using osub_reflexive.
Qed.
Lemma osub_transitive: forall o1 o2 o3, osub o1 o2 -> osub o2 o3 -> osub o1 o3.
Proof.
unfold osub.
intros ? ? ? hs1 hs2 a3 h3.
generalize (hs2 _ h3); intros [ a2 [ h2 ? ]].
generalize (hs1 _ h2); intros [ a1 [ h1 ? ]].
eauto.
Qed.
Lemma subsume_transitive: forall e1 e2 e3, subsume e1 e2 -> subsume e2 e3 -> subsume e1 e3.
Proof.
unfold subsume.
eauto using osub_transitive.
Qed.
Lemma subsume_empty: forall e, subsume e (@empty _).
Proof.
unfold subsume.
intros.
rewrite lookup_empty_None.
apply osub_None.
Qed.
Lemma subsume_insert: forall e1 e2, subsume e1 e2 -> forall x o1 o2, osub o1 o2 -> subsume (raw_insert x o1 e1) (raw_insert x o2 e2).
Proof.
unfold subsume.
do 7 intro.
intros n.
case (le_gt_dec x n); [ case (eq_nat_dec x n) | ]; intros; (* In each case, [lookup_insert] simplifies the goal. *) repeat lookup_insert; eauto.
Qed.
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
eauto.
Qed.
Lemma subsume_cons_cons_inversion: forall o1 o2 e1 e2, subsume (o1 :: e1) (o2 :: e2) -> osub o1 o2 /\ subsume e1 e2.
Proof.
do 4 intro.
intro h.
split.
-
eapply (h 0).
-
intro n.
eapply (h (1 + n)).
Qed.
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
}
Qed.
Lemma subsume_map: forall f, (forall a1 a2, sub a1 a2 -> sub (f a1) (f a2)) -> forall e1 e2, subsume e1 e2 -> subsume (map f e1) (map f e2).
Proof.
intros ? hf ? ? hs.
intros ? b2 hlm2.
generalize (lookup_map_some_reverse _ _ _ hlm2); intros [ ? [ hl2 ? ]].
subst.
generalize (hs _ _ hl2); intros [ a1 [ ? ? ]].
eauto using lookup_map_some.
Qed.
End Subsume.
Hint Resolve osub_reflexive osub_Some_Some subsume_reflexive subsume_transitive subsume_empty subsume_insert subsume_map : subsume.
Fixpoint concat (A : Type) (e1 : env A) (e2 : list A) : env A := match e2 with | nil => e1 | cons a e2 => concat (insert 0 a e1) e2 end.
Lemma lia_hint_1: forall n, n <= (n + 1) - 1.
Proof.
intros.
lia.
Qed.
Lemma length_concat: forall A (e2 : list A) (e1 : env A) n1 n, length e1 <= n1 -> n1 + length e2 = n -> length (concat e1 e2) <= n.
Proof.
induction e2; simpl; intros.
-
replace n with n1 by lia.
assumption.
-
eauto using length_insert, lia_hint_1 with lia.
Qed.
Hint Resolve length_concat : length construction_closed.
Lemma agree_concat: forall A (e : list A) (e1 e2 : env A) k n, agree e1 e2 k -> k + length e = n -> agree (concat e1 e) (concat e2 e) n.
Proof.
induction e; simpl; intros.
-
replace n with k by lia.
assumption.
-
eauto using agree_insert with lia.
Qed.
Hint Resolve agree_concat : agree.
Lemma insert_concat: forall (A : Type) n x nx (o : option A) e1 e2, length e2 = n -> n + x = nx -> raw_insert nx o (concat e1 e2) = concat (raw_insert x o e1) e2.
Proof.
induction n; intros; subst; destruct e2; simpl in *; try discriminate; auto.
-
rewrite insert_insert by lia.
erewrite <- (IHn (1 + x)) by first [ congruence | eauto ].
eauto with f_equal lia.
Qed.
Lemma concat_app: forall (A : Type) e1 (e2 e3 : list A), concat e1 (e2 ++ e3) = concat (concat e1 e2) e3.
Proof.
intros A e1 e2 e3.
generalize e1.
clear e1.
induction e2; intro e1; simpl; auto.
Qed.
Fixpoint replicate (A : Type) (n : nat) (a : A) : list A := match n with | 0 => @nil _ | S n => cons a (replicate n a) end.
Lemma length_replicate: forall (A : Type) n (a : A), length (replicate n a) = n.
Proof.
induction n; simpl; auto.
Qed.
Lemma insert_concat_replicate: forall (A : Type) n x nx (a : option A) (b : A) e1, n + x = nx -> raw_insert nx a (concat e1 (replicate n b)) = concat (raw_insert x a e1) (replicate n b).
Proof.
eauto using insert_concat, length_replicate.
Qed.
Lemma concat_replicate_is_iterated_insert: forall (A : Type) n (a : A) e, insert n a (concat e (replicate n a)) = concat e (replicate (S n) a).
Proof.
intros.
simpl.
eauto using insert_concat, length_replicate.
Qed.
Hint Resolve insert_concat length_replicate insert_concat_replicate concat_replicate_is_iterated_insert : insert_concat.
Lemma length_concat_replicate: forall A (a : A) (e1 : env A) n1 n2 n, length e1 <= n1 -> n1 + n2 = n -> length (concat e1 (replicate n2 a)) <= n.
Proof.
intros.
eapply length_concat.
eauto.
rewrite length_replicate.
eauto.
Qed.
Hint Resolve length_concat_replicate : length construction_closed.
Global Opaque empty lookup raw_insert map.
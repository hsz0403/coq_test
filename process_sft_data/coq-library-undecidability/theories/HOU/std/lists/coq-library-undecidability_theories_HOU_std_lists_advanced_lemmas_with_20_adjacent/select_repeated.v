Require Import List Arith Lia.
Import ListNotations.
From Undecidability.HOU Require Import std.tactics std.lists.basics std.decidable.
Set Default Proof Using "Type".
Notation nth := nth_error.
Section Nth.
Variable (X Y: Type).
End Nth.
Section Nats.
Fixpoint nats (n: nat) := match n with | 0 => nil | S n => 0 :: map S (nats n) end.
End Nats.
Hint Rewrite length_nats : listdb.
Section Tabulate.
Implicit Type X: Type.
Fixpoint tab {X} (f: nat -> X) k := match k with | 0 => nil | S n => tab f n ++ [f n] end.
End Tabulate.
Hint Rewrite tab_length tab_id_nats : listdb.
Section Repeated.
Variable (X Y: Type).
Implicit Types (x y: X) (n m: nat) (f: X -> Y).
End Repeated.
Hint Rewrite repeated_length repeated_map repeated_plus repeated_rev: listdb.
Section Select.
Context {X: Type}.
Fixpoint select (A: list nat) (B: list X) := match A with | nil => nil | i :: A => match nth B i with | Some x => x :: select A B | None => select A B end end.
End Select.
Section Find.
Context {X: Type}.
Context {D: Dis X}.
Fixpoint find (x: X) (A: list X) : option nat := match A with | nil => None | y :: A => if x == y then Some 0 else option_map S (find x A) end.
End Find.
Section Remove.
Variable (X: Type) (D: Dis X).
End Remove.
Section FlatMap.
Variable (X Y: Type).
Implicit Types (A B: list X) (f: X -> list Y).
End FlatMap.

Lemma tab_map X Y (f: nat -> X) (g: X -> Y) k: map g (tab f k) = tab (fun x => g (f x)) k.
Proof.
Admitted.

Lemma tab_S X (f: nat -> X) n: tab f (S n) = f 0 :: tab (fun k => f (S k)) n.
Proof.
induction n; cbn; eauto.
Admitted.

Lemma tab_plus X (f: nat -> X) n m: tab f (n + m) = tab f n ++ tab (fun k => f (n + k)) m.
Proof.
induction n in f |-*; eauto.
Admitted.

Lemma tab_map_nats X k (f: nat -> X): tab f k = map f (nats k).
Proof.
induction k in f |-*; eauto.
Admitted.

Lemma tab_id_nats k: tab id k = nats k.
Proof.
Admitted.

Lemma tab_nth {X} n m (f: nat -> X): n < m -> nth (tab f m) n = Some (f n).
Proof.
induction 1; cbn.
+
rewrite nth_error_app2, tab_length, Nat.sub_diag; cbn; eauto.
rewrite tab_length; eauto.
+
rewrite nth_error_app1; eauto.
Admitted.

Lemma tab_ext {X} (f g: nat -> X) n: (forall x, f x = g x) -> tab f n = tab g n.
Proof.
rewrite !tab_map_nats.
Admitted.

Lemma repeated_in x n y: y ∈ repeat x n -> x = y.
Proof.
Admitted.

Lemma repeated_plus n m x: repeat x (n + m) = repeat x n ++ repeat x m.
Proof.
Admitted.

Lemma repeated_rev n x: rev (repeat x n) = repeat x n.
Proof.
induction n; cbn; eauto.
rewrite IHn.
change [x] with (repeat x 1).
rewrite <-repeated_plus.
rewrite plus_comm.
Admitted.

Lemma repeated_map n x f: map f (repeat x n) = repeat (f x) n.
Proof.
Admitted.

Lemma repeated_length n x: length (repeat x n) = n.
Proof.
Admitted.

Lemma repeated_equal n y A: (forall x, x ∈ A -> x = y) -> length A = n -> repeat y n = A.
Proof.
induction A in n |-*; destruct n; cbn; eauto; try discriminate.
injection 2.
rewrite IHA; eauto.
intros.
Admitted.

Lemma repeated_incl x n A: x ∈ A -> repeat x n ⊆ A.
Proof.
Admitted.

Lemma repeated_tab (x: X) n: repeat x n = tab (Basics.const x) n.
Proof.
induction n; eauto; cbn [tab].
replace (S n) with (n + 1) by lia.
rewrite repeated_plus; cbn.
Admitted.

Lemma nth_error_repeated (x: X) n k : k < n -> nth (repeat x n) k = Some x.
Proof.
intros H.
erewrite repeated_tab, tab_map_nats, map_nth_error; eauto.
Admitted.

Lemma repeated_app_inv n x A B: repeat x n = A ++ B -> n = length A + length B /\ A = repeat x (length A) /\ B = repeat x (length B).
Proof.
induction n in A, B |-*.
-
cbn; destruct A, B; try discriminate.
intuition.
-
destruct A; cbn; try discriminate.
+
destruct B; try discriminate.
injection 1.
intuition.
cbn; now rewrite <-H0, repeated_length.
subst.
cbn; now rewrite repeated_length.
+
injection 1; intros; edestruct IHn; eauto.
intuition.
Admitted.

Lemma select_nil I: select I nil = nil.
Proof.
induction I; cbn.
-
reflexivity.
-
destruct nth eqn: H; eauto.
Admitted.

Lemma select_S I (x: X) A: select (map S I) (x :: A) = select I A.
Proof.
induction I.
-
reflexivity.
-
cbn.
rewrite IHI.
Admitted.

Lemma select_nats k A: select (nats k) A = firstn k A.
Proof.
induction k in A |-*.
-
reflexivity.
-
destruct A.
+
rewrite select_nil; reflexivity.
+
cbn.
rewrite select_S, IHk.
Admitted.

Lemma select_incl I A: select I A ⊆ A.
Proof.
induction I; cbn; intuition.
destruct nth eqn: H1; intuition.
eapply nth_error_In in H1.
Admitted.

Lemma incl_select A B: A ⊆ B -> exists I, I ⊆ nats (length B) /\ select I B = A.
Proof.
induction A.
+
exists nil.
lauto.
+
intros; destruct IHA as [I []]; lauto.
specialize (H a).
mp H; lauto.
eapply In_nth_error in H as [i].
exists (i::I).
cbn.
rewrite H, H1.
split; lauto.
Admitted.

Lemma select_map X Y (f: X -> Y) I A: map f (select I A) = select I (map f A).
Proof.
induction I in A |-*; cbn; eauto.
rewrite nth_error_map_option.
Admitted.

Lemma find_Some x A n: find x A = Some n -> nth A n = Some x.
Proof.
induction A in n |-*; cbn.
-
discriminate.
-
destruct (x == a).
injection 1; intros; subst.
reflexivity.
destruct find; try discriminate.
cbn; injection 1; intros; subst.
cbn.
Admitted.

Lemma find_in x A: x ∈ A -> exists n, find x A = Some n.
Proof.
induction A; cbn; intuition.
-
exists 0.
destruct (x == a); subst; intuition.
-
destruct (x == a).
+
subst; exists 0; intuition.
+
destruct H as [m]; exists (S m); intuition.
Admitted.

Lemma find_Some_nth x A n: nth A n = Some x -> exists k, find x A = Some k.
Proof.
Admitted.

Lemma find_not_in x A: find x A = None -> ~ x ∈ A.
Proof.
Admitted.

Lemma find_map f A n x: find x A = Some n -> exists m, find (f x) (map f A) = Some m.
Proof.
induction A in n |-*; cbn; try discriminate.
destruct eq_dec; intuition; subst.
-
exists 0; destruct eq_dec; intuition.
-
destruct (find x A); try discriminate.
edestruct IHA as [m]; eauto.
destruct eq_dec; eauto.
exists (S m).
Admitted.

Lemma find_map_inv X Y {D1: Dis X} {D2: Dis Y} y (f: X -> Y) (A: list X) (n: nat): find y (map f A) = Some n -> exists x, f x = y /\ find x A = Some n.
Proof.
induction A in y, n |-*; cbn; intuition; try discriminate.
destruct eq_dec.
+
injection H as ?; subst; exists a; intuition.
destruct eq_dec; intuition.
+
destruct find eqn: H1; try discriminate.
injection H as ?; subst.
eapply IHA in H1 as []; intuition; subst.
exists x.
intuition; destruct eq_dec; cbn; try congruence.
Admitted.

Lemma remove_remain (x y: X) A: x ∈ A -> x <> y -> x ∈ remove eq_dec y A.
Proof.
induction A; cbn; intuition; subst.
-
destruct (y == x); subst; intuition.
-
Admitted.

Lemma remove_prev (x y: X) (A: list X): y ∈ remove eq_dec x A -> y ∈ A.
Proof.
induction A; intuition.
cbn in H.
destruct (x == a); subst; intuition.
Admitted.

Lemma flat_map_app f A B: flat_map f (A ++ B) = flat_map f A ++ flat_map f B.
Proof.
Admitted.

Lemma flat_map_incl (f: X -> list Y) A B: A ⊆ B -> flat_map f A ⊆ flat_map f B.
Proof.
intros H x [y []] % in_flat_map.
Admitted.

Lemma flat_map_in_incl f a A: a ∈ A -> f a ⊆ flat_map f A.
Proof.
Admitted.

Lemma select_repeated n I x: I ⊆ nats n -> select I (repeat x n) = repeat x (length I).
Proof.
induction I; cbn; eauto; intros.
rewrite IHI; eauto with listdb.
edestruct (nth_error_lt_Some) as [y H']; try rewrite H'.
eapply nats_lt; lsimpl; firstorder.
now eapply nth_error_In, repeated_in in H'; subst.

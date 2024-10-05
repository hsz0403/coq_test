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

Lemma nth_error_map_option n (f: X -> Y) (A: list X): nth_error (map f A) n = option_map f (nth_error A n).
Proof.
destruct (nth_error A n) eqn: H1.
+
eapply map_nth_error in H1.
rewrite H1.
reflexivity.
+
eapply nth_error_None in H1.
eapply nth_error_None.
Admitted.

Lemma nth_error_lt_Some Z m (L: list Z): m < length L -> exists a, nth L m = Some a.
Proof.
intros H % nth_error_Some.
destruct nth; intuition.
Admitted.

Lemma nth_error_Some_lt Z m a (L: list Z): nth L m = Some a -> m < length L.
Proof.
Admitted.

Lemma nats_lt: forall k i, i ∈ nats k -> i < k.
Proof.
induction k; cbn; intuition.
lia.
eapply in_map_iff in H0.
destruct H0; intuition; subst.
Admitted.

Lemma nth_nats m k: m < k -> nth (nats k) m = Some m.
Proof.
induction k in m |-*.
-
lia.
-
intros; destruct m; cbn in *; eauto.
erewrite map_nth_error; eauto.
Admitted.

Lemma lt_nats x k: x < k -> x ∈ nats k.
Proof.
Admitted.

Lemma incl_nats I k: I ⊆ nats k -> forall i, i ∈ I -> i < k.
Proof.
Admitted.

Lemma nats_incl I k: (forall i, i ∈ I -> i < k) -> I ⊆ nats k.
Proof.
Admitted.

Lemma length_nats k: length (nats k) = k.
Proof.
Admitted.

Lemma tab_length X (f: nat -> X) k: length (tab f k) = k.
Proof.
Admitted.

Lemma tab_map X Y (f: nat -> X) (g: X -> Y) k: map g (tab f k) = tab (fun x => g (f x)) k.
Proof.
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

Lemma select_repeated n I x: I ⊆ nats n -> select I (repeat x n) = repeat x (length I).
Proof.
induction I; cbn; eauto; intros.
rewrite IHI; eauto with listdb.
edestruct (nth_error_lt_Some) as [y H']; try rewrite H'.
eapply nats_lt; lsimpl; firstorder.
Admitted.

Lemma select_incl I A: select I A ⊆ A.
Proof.
induction I; cbn; intuition.
destruct nth eqn: H1; intuition.
eapply nth_error_In in H1.
Admitted.

Lemma tab_S X (f: nat -> X) n: tab f (S n) = f 0 :: tab (fun k => f (S k)) n.
Proof.
induction n; cbn; eauto.
cbn in *; now rewrite IHn.

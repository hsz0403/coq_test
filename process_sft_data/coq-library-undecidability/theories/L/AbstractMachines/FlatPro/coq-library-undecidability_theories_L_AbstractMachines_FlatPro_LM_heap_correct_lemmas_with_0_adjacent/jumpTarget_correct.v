From Undecidability.L Require Import Util.L_facts Complexity.ResourceMeasures.
From Undecidability.L Require Import LM_heap_def.
Import Lia.
Definition extended (H H' : Heap) := forall alpha m, nth_error H alpha = Some m -> nth_error H' alpha = Some m.
Import L_Notations.
Inductive unfolds H a: nat -> term -> term -> Prop := | unfoldsUnbound k n : n < k -> unfolds H a k (var n) (var n) | unfoldsBound k b P s s' n: n >= k -> lookup H a (n-k) = Some (b,P) -> reprP P s -> unfolds H b 0 s s' -> unfolds H a k (var n) s' | unfoldsLam k s s': unfolds H a (S k) s s' -> unfolds H a k (lam s) (lam s') | unfoldsApp k (s t s' t' : term): unfolds H a k s s' -> unfolds H a k t t' -> unfolds H a k (s t) (s' t').
Definition unfolds_ind' (H : Heap) (P : HAdd -> nat -> term -> term -> Prop) (f : forall (a : HAdd) (k n : nat), n < k -> P a k n n) (f0 : forall (a : HAdd) (k : nat) (b : HAdd) (P0 : list Tok) (s s' : term) (n : nat), n >= k -> lookup H a (n - k) = Some (b, P0) -> P0 = compile s -> unfolds H b 1 s s' -> P b 1 s s' -> P a k n (lam s')) (f1 : forall (a : HAdd) (k : nat) (s s' : term), unfolds H a (S k) s s' -> P a (S k) s s' -> P a k (lam s) (lam s')) (f2 : forall (a : HAdd) (k : nat) (s t s' t' : term), unfolds H a k s s' -> P a k s s' -> unfolds H a k t t' -> P a k t t' -> P a k (s t) (s' t')) : forall (a : HAdd) (n : nat) (t t0 : term), unfolds H a n t t0 -> P a n t t0.
Proof.
intros a n s t.
induction t in a,n,s,t|-*;intros Ht.
all:inv Ht.
all:eauto.
-
now inv H2.
-
now inv H2.
-
inv H2.
inv H3.
eapply f0.
all:try reflexivity;try eassumption.
eauto.
Definition unfolds_rect (H : Heap) (P : HAdd -> nat -> term -> term -> Type) (f : forall (a : HAdd) (k n : nat), n < k -> P a k n n) (f0 : forall (a : HAdd) (k : nat) (b : HAdd) (P0 : list Tok) (s s' : term) (n : nat), n >= k -> lookup H a (n - k) = Some (b, P0) -> P0 = compile s -> unfolds H b 1 s s' -> P b 1 s s' -> P a k n (lam s')) (f1 : forall (a : HAdd) (k : nat) (s s' : term), unfolds H a (S k) s s' -> P a (S k) s s' -> P a k (lam s) (lam s')) (f2 : forall (a : HAdd) (k : nat) (s t s' t' : term), unfolds H a k s s' -> P a k s s' -> unfolds H a k t t' -> P a k t t' -> P a k (s t) (s' t')) : forall (a : HAdd) (n : nat) (t t0 : term), unfolds H a n t t0 -> P a n t t0.
Proof.
intros a n s t.
induction t in a,n,s,t|-*;intros Ht.
-
enough (s=n0).
{
subst;apply f;inv Ht.
easy.
now inv H5.
}
inv Ht.
easy.
now inv H3.
-
destruct s.
3:now exfalso.
1:{
exfalso;inv Ht.
now inv H5.
}
eapply f2.
2:eapply IHt1.
4:eapply IHt2.
all:now inv Ht.
-
destruct s.
2:now exfalso.
+
destruct (lookup H a (n0 - n)) as [[b Q]|] eqn:Hlook.
2:{
exfalso;inv Ht.
congruence.
}
destruct (decompile 0 Q []) as [[|s]|]eqn:HQ.
1,3:now exfalso; inv Ht; rewrite Hlook in H2; injection H2 as [= -> ->]; inv H3; now rewrite decompile_correct in HQ.
eapply f0.
now inv Ht.
eassumption.
3:eapply IHt.
all:inv Ht; rewrite Hlook in H2; injection H2 as [= <- <-]; inv H3; rewrite decompile_correct in HQ.
injection HQ as [= ->].
reflexivity.
all:now inv H5.
+
eapply f1.
now inv Ht.
eapply IHt.
now inv Ht.
Inductive reprC : Heap -> _ -> term -> Prop := reprCC H P s a s' : reprP P s -> unfolds H a 0 s s' -> reprC H (a,P) s'.
Instance extended_PO : PreOrder extended.
Proof.
unfold extended;split;repeat intro.
all:eauto.
Typeclasses Opaque extended.
Instance unfold_extend_Proper : Proper (extended ==> eq ==> eq ==> eq ==> eq ==>Basics.impl) unfolds.
Proof.
repeat intro.
subst.
eapply unfolds_extend.
all:eassumption.
Instance reprC_extend_Proper : Proper (extended ==> eq ==> eq ==>Basics.impl) reprC.
Proof.
repeat intro.
subst.
eapply reprC_extend.
all:eassumption.
Definition init s :state := ([(0,compile s)],[],[]).

Lemma jumpTarget_correct s c: jumpTarget 0 [] (compile s ++ retT::c) = Some (compile s,c).
Proof.
change (Some (compile s,c)) with (jumpTarget 0 ([]++compile s) (retT::c)).
generalize 0.
generalize (retT::c) as c'.
clear c.
generalize (@nil Tok) as c.
induction s;intros c' c l.
-
reflexivity.
-
cbn.
autorewrite with list.
rewrite IHs1,IHs2.
cbn.
now autorewrite with list.
-
cbn.
autorewrite with list.
rewrite IHs.
cbn.
now autorewrite with list.

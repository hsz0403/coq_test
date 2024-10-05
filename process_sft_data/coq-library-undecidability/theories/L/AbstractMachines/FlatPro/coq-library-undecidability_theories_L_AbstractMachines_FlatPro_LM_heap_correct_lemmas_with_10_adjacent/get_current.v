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

Lemma put_extends H H' m b: put H m = (b,H') -> extended H H'.
Proof.
unfold extended,put.
intros [= <- <-] ? ? ?.
Admitted.

Lemma tailRecursion_compile s P a T: tailRecursion (a,compile s ++ P) T = ((a,compile s ++ P))::T.
Proof.
induction s in P,T|-*.
all:cbn [compile].
1,3:easy.
rewrite <- !app_assoc.
rewrite IHs1.
Admitted.

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
Admitted.

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
Admitted.

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
Admitted.

Lemma unfolds_bound H k s s' a: unfolds H a k s s' -> bound k s'.
Proof.
induction 1.
-
now constructor.
-
inv H2.
inv H3.
constructor.
inv IHunfolds.
eapply bound_ge.
eauto.
lia.
-
now constructor.
-
Admitted.

Lemma reprC_elim H g s': reprC H g s' -> { s | reprP (snd g) s /\ unfolds H (fst g) 0 s s'}.
Proof.
destruct g as [a Q];cbn.
intros Hg.
destruct (decompile 0 Q []) as [[|s]|] eqn:H'.
1,3:now exfalso; inv Hg; inv H4; rewrite decompile_correct in H'.
exists (lam s).
inv Hg; inv H4; rewrite decompile_correct in H'.
inv H'.
Admitted.

Lemma reprC_elim_deep H g t: reprC H g t -> exists s t' a, g = (a,compile s) /\ t = lam t' /\ unfolds H a 1 s t'.
Proof.
intros (s&HP&?Hu)%reprC_elim.
apply reprP_elim in HP as (?&?&?).
destruct g.
cbn in *.
subst.
inv Hu.
Admitted.

Lemma unfolds_inv_lam_lam H a k s s': unfolds H a k (lam s) (lam s') -> unfolds H a (S k) s s'.
Proof.
Admitted.

Lemma unfolds_subst' H s s' t' a a' k g: nth_error (A:=HEntr) H a' = Some (Some (g,a)) -> reprC H g t' -> unfolds H a (S k) s s' -> unfolds H a' k s (subst s' k t').
Proof.
intros H1 R I__s.
remember (S k) as k' eqn:eq__k.
induction I__s in H1,k,eq__k|-*.
all:subst k0.
-
cbn.
destruct (Nat.eqb_spec n k).
+
assert (H':lookup H a' (n-k) = Some g).
{
subst n.
cbn.
rewrite Nat.sub_diag.
cbn.
rewrite H1.
reflexivity.
}
inv R.
decide _.
econstructor.
all:eauto.
econstructor.
all:eauto.
+
decide _.
econstructor; eauto.
lia.
econstructor.
lia.
-
rename s into u.
assert (H':lookup H a' (n-k) = Some (b,P)).
{
destruct n.
lia.
rewrite Nat.sub_succ_l.
cbn.
rewrite H1.
now rewrite Nat.sub_succ in H2.
lia.
}
rewrite bound_closed_k.
2:{
eapply bound_ge with (k:=0).
2:lia.
now eauto using unfolds_bound.
}
econstructor.
all:try eassumption;lia.
-
econstructor.
all:eauto.
-
econstructor.
all:eauto.
Unshelve.
Admitted.

Lemma get_current H m H' alpha : put H m = (alpha,H') -> nth_error H' alpha = Some m.
Proof.
unfold put.
intros [= <- <-].
rewrite nth_error_app2.
now rewrite <- minus_n_n.
reflexivity.

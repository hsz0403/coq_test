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

Lemma soundness' s0 s P a T V H k sigma: evaluatesIn step k ((a,compile s0++P)::T,V,H) sigma -> unfolds H a 0 s0 s -> exists k1 k2 g H' t n , k = k1 + k2 /\ pow step k1 ((a,compile s0++P)::T,V,H) (tailRecursion (a,P) T,g::V,H') /\ evaluatesIn step k2 (tailRecursion (a,P) T,g::V,H') sigma /\ timeBS n s t /\ extended H H' /\ reprC H' g t /\ k1 = 3*n + 1.
Proof.
intros [R Ter].
unfold HClos in *.
revert s s0 P a T V H R.
induction k as [k IH] using lt_wf_ind .
intros s s0 P a T V H R Unf.
induction s0 as [|s01 IHs01 s02 IHs02 | s0] in IH,k,s,Unf,T,R,P,V,H|-*.
-
inv Unf.
lia.
assert (exists k', k = 1 + k') as (k'&->).
{
destruct k.
2:eauto.
exfalso.
inv R.
eapply Ter.
econstructor.
rewrite Nat.sub_0_r in *.
eassumption.
}
apply pow_add in R as (?&R1&R2).
apply rcomp_1 in R1.
inv R1.
rewrite Nat.sub_0_r in *.
rewrite H12 in H2.
inv H2.
inv H3.
inv H5.
repeat esplit.
+
cbn.
constructor.
eassumption.
+
eassumption.
+
eauto.
+
econstructor.
+
reflexivity.
+
eauto using unfolds.
+
lia.
-
cbn in R.
inversion Unf as [| | | tmp1 tmp2 tmp3 tmp4 tmp5 Unf1 Unf2].
subst tmp1 tmp2 tmp3 s.
rewrite <- !app_assoc in R.
pose (R':=R).
eapply IHs01 in R' as (k11&k12&[a' s1']&H'1&t1&n1&eq1&R11&[R12 _]&Ev1&Ext1&Rg1&eqn1).
3:eassumption.
rewrite tailRecursion_compile in R12.
pose (R':=R12).
eapply IHs02 in R' as (k21&k22&g2&H'2&t2&n2&eq2&R21&[R22 _]&Ev2&Ext2&Rg2&eqn2).
3-4:now eauto using unfolds_extend.
2:{
intros.
eapply IH.
lia.
all:eauto.
}
setoid_rewrite Ext2 in Rg1.
cbn in R22.
assert (exists k22', k22 = 1 + k22') as (k22'&->).
{
destruct k22.
2:eauto.
exfalso.
inv R22.
eapply Ter.
econstructor.
reflexivity.
}
pose (R':=R22).
apply pow_add in R' as (?&R2'&R3).
apply rcomp_1 in R2'.
inversion R2' as [ | AA BB CC DD EE KK H3' b GG HH eqH'2 JJ| ].
subst AA BB CC EE GG HH DD KK.
subst x.
specialize (put_extends eqH'2) as Ext3.
inversion Rg1 as [AA BB t1'0 CC t1' Unft'].
subst AA BB CC t1.
destruct Unft'.
inversion H0 as [| | AA BB t1'' unf''' EE FF |].
subst AA BB t1'.
clear H0.
edestruct IH with (P:=@nil Tok) as (k31&k32&g3&H'3&t3&n3&eq3&R31&[R32 _]&Ev3&Ext3'&Rg3&eqn3).
2:{
autorewrite with list.
exact R3.
}
now nia.
{
eapply unfolds_subst.
-
eauto using get_current.
-
now rewrite <- Ext3.
-
eapply unfolds_extend.
2:eassumption.
easy.
}
unfold tailRecursion at 1 in R32.
inversion Rg2 as [AAA BBB CCC DDD EEE FFF GGG HHH III].
subst AAA g2 EEE.
inversion FFF.
subst BBB CCC.
inversion GGG.
subst t2.
inversion Rg3 as [AA BB CC DD EE FF].
subst g3 AA EE.
destruct FF.
eexists (k11+(k21+(1+k31))),k32,_,_,_.
repeat eexists.
+
lia.
+
cbn [compile].
autorewrite with list.
rewrite app_nil_r in R31.
unfold tailRecursion in R31 at 2.
repeat (eapply pow_add with (R:=step);eexists;split).
*
eassumption.
*
rewrite tailRecursion_compile.
eassumption.
*
cbn.
eapply rcomp_1 with (R:=step).
constructor.
eassumption.
*
eassumption.
+
eassumption.
+
eassumption.
+
econstructor.
all:eauto.
+
now rewrite Ext1,Ext2,Ext3.
+
eauto using unfolds.
+
lia.
-
inv Unf.
assert (exists k', k = 1 + k') as (k'&->).
{
destruct k.
2:eauto.
exfalso.
inv R.
eapply Ter.
cbn.
econstructor.
autorewrite with list.
eapply jumpTarget_correct.
}
apply pow_add in R as (?&R1&R2).
apply rcomp_1 in R1.
inv R1.
autorewrite with list in H8.
cbn in H8.
rewrite jumpTarget_correct in H8.
inv H8.
eexists 1,k',_,_,_.
repeat esplit.
+
cbn.
constructor.
autorewrite with list.
apply jumpTarget_correct.
+
eassumption.
+
eauto.
+
constructor.
+
reflexivity.
+
eauto using unfolds.
+
lia.

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

Lemma completenessInformative' s t k s0 P a T V H: timeBS k s t -> unfolds H a 0 s0 s -> {g & {l &{H' & reprC H' g t /\ pow step l ((a,compile s0++P)::T,V,H) (tailRecursion (a,P) T,g::V,H') /\ l = 3*k+1 /\ extended H H'}}}.
Proof.
intros Ev.
revert s0 P a T V H.
induction Ev using timeBS_rect;intros * R.
-
destruct s0.
2:now exfalso.
+
edestruct (lookup H a n) as [[b Q]|] eqn:?.
2:{
exfalso;inv R;rewrite Nat.sub_0_r in *;congruence.
}
eexists (b,Q),1,H.
repeat split.
*
inv R.
rewrite Nat.sub_0_r in *.
exists s0.
all:congruence.
*
cbn [compile].
rewrite <- rcomp_1.
now econstructor.
*
hnf.
tauto.
+
eexists (a,compile _),1,H.
repeat split.
*
inv R.
eauto using reprC,reprP,unfolds.
*
cbn [compile Datatypes.app]; autorewrite with list;cbn [Datatypes.app].
rewrite <- rcomp_1.
constructor.
apply jumpTarget_correct.
*
hnf.
tauto.
-
destruct s0.
1,3:exfalso;inv R.
now inv H6.
rename s0_1 into t1, s0_2 into t2.
assert (I__s : unfolds H0 a 0 t1 s) by now inv R.
assert (I__t : unfolds H0 a 0 t2 t) by now inv R.
cbn [compile List.app]; autorewrite with list; cbn [List.app].
specialize (IHEv1 _ (compile t2 ++ appT ::P) _ T V _ I__s) as ([a2 P__temp]&k1&Heap1&rep1&R1&eq_k1&Ext1).
eapply reprC_elim in rep1 as (?&?&I__s');cbn [fst snd]in *.
destruct x.
1,2:now exfalso.
eapply unfolds_inv_lam_lam in I__s'.
replace P__temp with (compile x) in * by now inv H1.
clear H1.
apply (unfolds_extend Ext1) in I__t.
specialize (IHEv2 _ (appT ::P) _ T ((a2,compile x)::V) _ I__t) as (g__t&k2&Heap2&rep2&R2&e_k2&Ext2).
edestruct (put Heap2 (Some(g__t,a2))) as [a2' Heap2'] eqn:eq.
assert (Ext2' := (put_extends eq)).
apply ( reprC_extend Ext2') in rep2.
apply ( unfolds_extend Ext2) in I__s'.
apply ( unfolds_extend Ext2') in I__s'.
eassert (I__subst := unfolds_subst (get_current eq) rep2 I__s').
edestruct (IHEv3 _ [] _ (tailRecursion (a,P) T) V _ I__subst) as (g__u&k3&Heap3&rep3&R3&eq_k3&Ext3).
eexists g__u,_,Heap3.
split;[ | split;[|split]].
+
eassumption.
+
apply pow_add.
eexists.
split.
{
exact R1.
}
apply pow_add.
eexists.
split.
{
rewrite tailRecursion_compile.
exact R2.
}
apply pow_add.
eexists.
split.
{
apply (rcomp_1 step).
constructor;eassumption.
}
{
rewrite app_nil_r in R3.
exact R3.
}
+
nia.
+
rewrite Ext1,Ext2,Ext2',Ext3.
reflexivity.

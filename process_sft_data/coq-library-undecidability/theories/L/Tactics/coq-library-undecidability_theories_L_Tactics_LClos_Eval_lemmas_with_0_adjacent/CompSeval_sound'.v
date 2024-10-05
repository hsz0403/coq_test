From Undecidability.L.Tactics Require Export LClos.
Require Import FunInd.
Open Scope LClos.
Definition CompBeta s t := match s,t with |CompClos (lam ls) A,CompClos (lam lt) B => Some (CompClos ls (CompClos (lam lt) B::A)) |_,_ => None end.
Definition CompAppCount j u v := match u,v with (l,u),(k,v) => (j+(l+k),CompApp u v) end.
Fixpoint CompSeval n (u: nat * Comp) : nat * Comp:= match n with S n => match u with | (l,CompApp s t) => match CompBeta s t with | Some u => CompSeval n (S l,u) | None => CompSeval n (CompAppCount l (CompSeval n (0,s)) (CompSeval n (0,t))) end | (l,CompClos (app s t) A) => CompSeval n (l,(CompClos s A) (CompClos t A)) | (l,CompClos (var x) A) => (l,nth x A (CompVar x)) | u => u end | _ => u end.
Hint Resolve CompSeval_validComp : core.
Functional Scheme CompSeval_ind := Induction for CompSeval Sort Prop.

Lemma CompSeval_sound' n s l : let (k,t) := CompSeval n (l,s) in k >= l /\ s >[(k-l)] t.
Proof with (repeat inv_validComp;repeat (constructor || intuition|| subst ; eauto using star || rewrite Nat.sub_diag||cbn in *)).
pose (p:= (l,s)).
change (let (k, t) := CompSeval n p in k >= fst p /\ (snd p) >[(k-(fst p))] t).
generalize p.
clear l s p.
intros p.
functional induction (CompSeval n p); intros;cbn...
-
apply CompBeta_sound in e2.
destruct (CompSeval _ _);split...
eapply CPow_trans;try eassumption.
lia.
-
repeat destruct (CompSeval _ _)...
eapply CPow_trans...
-
repeat destruct (CompSeval _ _)...
eapply CPow_trans...

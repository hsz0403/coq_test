From Undecidability.L.Tactics Require Export LClos.
Require Import FunInd.
Open Scope LClos.
Definition CompBeta s t := match s,t with |CompClos (lam ls) A,CompClos (lam lt) B => Some (CompClos ls (CompClos (lam lt) B::A)) |_,_ => None end.
Definition CompAppCount j u v := match u,v with (l,u),(k,v) => (j+(l+k),CompApp u v) end.
Fixpoint CompSeval n (u: nat * Comp) : nat * Comp:= match n with S n => match u with | (l,CompApp s t) => match CompBeta s t with | Some u => CompSeval n (S l,u) | None => CompSeval n (CompAppCount l (CompSeval n (0,s)) (CompSeval n (0,t))) end | (l,CompClos (app s t) A) => CompSeval n (l,(CompClos s A) (CompClos t A)) | (l,CompClos (var x) A) => (l,nth x A (CompVar x)) | u => u end | _ => u end.
Hint Resolve CompSeval_validComp : core.
Functional Scheme CompSeval_ind := Induction for CompSeval Sort Prop.

Lemma CompSeval_validComp s k n: validComp s -> validComp (snd (CompSeval n (k,s))).
Proof with repeat (apply validCompApp ||apply validCompClos || eauto || congruence || subst || simpl in * || intuition).
revert s k.
induction n; intros s k vs...
inv vs...
case_eq (CompBeta s0 t);intros...
-
apply CompBeta_validComp in H1...
-
assert (IHn1 := IHn s0 0 H).
assert (IHn2 := IHn t 0 H0).
unfold snd in *.
do 2 destruct ((CompSeval n (_,_)))...
-
destruct s0...

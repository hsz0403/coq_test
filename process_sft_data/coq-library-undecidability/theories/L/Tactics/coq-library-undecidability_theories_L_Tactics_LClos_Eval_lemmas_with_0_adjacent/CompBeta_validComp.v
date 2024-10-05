From Undecidability.L.Tactics Require Export LClos.
Require Import FunInd.
Open Scope LClos.
Definition CompBeta s t := match s,t with |CompClos (lam ls) A,CompClos (lam lt) B => Some (CompClos ls (CompClos (lam lt) B::A)) |_,_ => None end.
Definition CompAppCount j u v := match u,v with (l,u),(k,v) => (j+(l+k),CompApp u v) end.
Fixpoint CompSeval n (u: nat * Comp) : nat * Comp:= match n with S n => match u with | (l,CompApp s t) => match CompBeta s t with | Some u => CompSeval n (S l,u) | None => CompSeval n (CompAppCount l (CompSeval n (0,s)) (CompSeval n (0,t))) end | (l,CompClos (app s t) A) => CompSeval n (l,(CompClos s A) (CompClos t A)) | (l,CompClos (var x) A) => (l,nth x A (CompVar x)) | u => u end | _ => u end.
Hint Resolve CompSeval_validComp : core.
Functional Scheme CompSeval_ind := Induction for CompSeval Sort Prop.

Lemma CompBeta_validComp s t u: validComp s -> validComp t -> CompBeta s t = Some u -> validComp u.
Proof with repeat (auto || congruence || subst || simpl in * || intuition).
intros vs vt eq.
inv vs; inv vt...
destruct s0...
destruct s,s0...
inv eq.
repeat constructor...
inv H1...

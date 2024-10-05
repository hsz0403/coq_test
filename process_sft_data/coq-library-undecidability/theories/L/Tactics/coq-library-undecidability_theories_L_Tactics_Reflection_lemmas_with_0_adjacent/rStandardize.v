From Undecidability.L Require Export Util.L_facts.
From Undecidability.L.Tactics Require Export LClos_Eval.
From Undecidability.L.Tactics Require Import mixedTactics.
Require Import FunInd.
Open Scope LClos.
Inductive rTerm : Type := | rVar (x : nat) : rTerm | rApp (s : rTerm) (t : rTerm) : rTerm | rLam (s : rTerm) | rConst (x : nat) : rTerm | rRho (s : rTerm).
Coercion rApp : rTerm >-> Funclass.
Definition denoteTerm (phi : nat -> term) :rTerm->term := fix denoteTerm s := match s with | rVar n => var n | rApp s t=> app (denoteTerm s) (denoteTerm t) | rLam s => lam (denoteTerm s) | rConst n => phi n | rRho s => rho (denoteTerm s) end.
Definition Proc phi := forall (n:nat) , proc (phi n).
Definition rClosed phi s:= Proc phi /\ closed (denoteTerm phi s).
Definition rPow phi n s t := denoteTerm phi s >(n) denoteTerm phi t.
Inductive rComp : Type := | rCompVar (x:nat) | rCompApp (s : rComp) (t : rComp) : rComp | rCompClos (s : rTerm) (A : list rComp) : rComp.
Coercion rCompApp : rComp >-> Funclass.
Definition denoteComp (phi : nat -> term) :rComp -> Comp:= fix denoteComp s := match s with | rCompVar x => CompVar x | rCompApp s t => (denoteComp s) (denoteComp t) | rCompClos s A => CompClos (denoteTerm phi s) (map denoteComp A) end.
Fixpoint rSubstList (s:rTerm) (x:nat) (A: list rTerm): rTerm := match s with | rVar n => if Dec ( n < x )then rVar n else nth (n-x) A (rVar n) | rApp s t => (rSubstList s x A) (rSubstList t x A) | rLam s => rLam (rSubstList s (S x) A) | rRho s => rRho (rSubstList s (S x) A) | rConst x => rConst x end.
Fixpoint rDeClos (s:rComp) : rTerm := match s with | rCompVar x => rVar x | rCompApp s t => (rDeClos s) (rDeClos t) | rCompClos s A => rSubstList s 0 (map rDeClos A) end.
Definition rComp_ind_deep' (P : rComp -> Prop) (Pl : list rComp -> Prop) (IHVar : forall x : nat, P (rCompVar x)) (IHApp : forall s : rComp, P s -> forall t : rComp, P t -> P (s t)) (IHClos : forall (s : rTerm) (A : list rComp), Pl A -> P (rCompClos s A)) (IHNil : Pl nil) (IHCons : forall (a:rComp) (A : list rComp), P a -> Pl A -> Pl (a::A)) (x:rComp) : P x := (fix f c : P c:= match c with | rCompVar x => IHVar x | rCompApp s t => IHApp s (f s) t (f t) | rCompClos s A => IHClos s A ((fix g A : Pl A := match A with [] => IHNil | a::A => IHCons a A (f a) (g A) end) A) end) x .
Definition rComp_ind_deep (P : rComp -> Prop) (IHVar : forall x : nat, P (rCompVar x)) (IHApp : forall s : rComp, P s -> forall t : rComp, P t -> P (s t)) (IHClos : forall (s : rTerm) (A : list rComp), (forall a, a el A -> P a) -> P (rCompClos s A)) : forall x, P x.
Proof.
apply rComp_ind_deep' with (Pl:=fun A => (forall a, a el A -> P a));auto.
-
intros.
inv H1;auto.
Definition rValidComp phi s := Proc phi /\validComp (denoteComp phi s).
Definition rCompBeta s t := match s,t with |rCompClos (rLam ls) A,rCompClos (rLam lt) B => Some (rCompClos ls (t::A)) |rCompClos (rLam ls) A,rCompClos (rConst x) B => Some (rCompClos ls (t::A)) |rCompClos (rLam ls) A,rCompClos (rRho lt) B => Some (rCompClos ls (t::A)) |_,_ => None end.
Definition rCompAppCount := fun (j : nat) (u v : nat * rComp) => let (l, u0) := u in let (k, v0) := v in (j + (l + k), u0 v0).
Fixpoint rCompSeval' n (u : nat*rComp) : (nat *rComp)*bool:= match n with S n => match u with | (l, rCompApp s t) => match rCompSeval' n (0,s),rCompSeval' n (0,t) with (i, s',true),(j, t',true) => match rCompBeta s' t' with Some u => rCompSeval' n ((S l)+(i+j),u) | None => ((l+(i+j),s' t'),false) end | ((i,s'),_),((j,t'),_) => ((l+(i+j),s' t'),false) end | (l, rCompClos (rApp s t) A ) => rCompSeval' n (l, rCompApp (rCompClos s A) (rCompClos t A)) | (l , rCompClos (rVar x) A )=> (l,nth x A (rCompVar x),true) | (l, rCompClos (rConst x) A )=> (u,true) | (l, rCompVar x ) => (u,true) | (l, rCompClos (rLam _) A) => (u,true) | (l, rCompClos (rRho _) A) => (u,true) end | 0 => (u,true) end.
Definition rCompSeval n u : (nat*rComp):= (fst (rCompSeval' n u)).
Functional Scheme rCompSeval'_ind := Induction for rCompSeval' Sort Prop.
Fixpoint rClosed_decb' n u : bool:= match u with | rApp s t => andb (rClosed_decb' n s) (rClosed_decb' n t) | rVar x => negb (leb n x) | rConst x => true | rLam s =>rClosed_decb' (S n) s | rRho s =>rClosed_decb' (S n) s end.
Definition rClosed_decb s:= rClosed_decb' 0 s.
Definition liftPhi Vars n:=nth n Vars I.
Arguments liftPhi Vars n/.
Fixpoint benchTerm x : rTerm := match x with 0 => (rLam (rVar 0)) | S x => (rLam (benchTerm x)) (rLam (rVar 0)) end.
Close Scope LClos.

Lemma rStandardize n phi s : Proc phi -> rClosed phi s -> let (l,s') := (rCompSeval n (0,rCompClos s [])) in rPow phi l s (rDeClos s').
Proof with eauto.
intros pp cl.
unfold rPow.
rewrite rClosed_valid in *;auto.
assert (cl': rValidComp phi (snd (rCompSeval n (0,rCompClos s [])))).
-
apply rCompSeval_rValidComp;auto.
-
destruct rCompSeval eqn:eq1.
rewrite !expandDenote;auto.
specialize (rCompSeval_sound n (rCompClos s []) 0 pp);intros H.
rewrite eq1 in H.
destruct H as [_ H].
rewrite <- minus_n_O in H.
rewrite <- rDeClos_reduce...
apply deClos_correct...
destruct cl...

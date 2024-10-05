From Undecidability.L Require Export Util.L_facts.
Inductive Comp : Type := | CompVar (x:nat) | CompApp (s : Comp) (t : Comp) : Comp | CompClos (s : term) (A : list Comp) : Comp.
Coercion CompApp : Comp >-> Funclass.
Inductive lamComp : Comp -> Prop := lambdaComp s A: lamComp (CompClos (lam s) A).
Inductive validComp : Comp -> Prop := | validCompApp s t : validComp s -> validComp t -> validComp (s t) | validCompClos (s : term) (A : list Comp) : (forall a, a el A -> validComp a) -> (forall a, a el A -> lamComp a) -> bound (length A) s -> validComp (CompClos s A).
Hint Constructors Comp lamComp validComp : core.
Definition validEnv A := forall a, a el A -> validComp a (*/\ lamComp a)*).
Definition validEnv' A := forall a, a el A -> closed a.
Hint Unfold validEnv validEnv' : core.
Ltac inv_validComp := match goal with | H : validComp (CompApp _ _) |- _ => inv H | H : validComp (CompClos _ _) |- _ => inv H end.
Definition Comp_ind_deep' (P : Comp -> Prop) (Pl : list Comp -> Prop) (IHVar : forall x : nat, P (CompVar x)) (IHApp : forall s : Comp, P s -> forall t : Comp, P t -> P (s t)) (IHClos : forall (s : term) (A : list Comp), Pl A -> P (CompClos s A)) (IHNil : Pl nil) (IHCons : forall (a:Comp) (A : list Comp), P a -> Pl A -> Pl (a::A)) (x:Comp) : P x := (fix f c : P c:= match c with | CompVar x => IHVar x | CompApp s t => IHApp s (f s) t (f t) | CompClos s A => IHClos s A ((fix g A : Pl A := match A with [] => IHNil | a::A => IHCons a A (f a) (g A) end) A) end) x .
Definition Comp_ind_deep (P : Comp -> Prop) (IHVar : forall x : nat, P (CompVar x)) (IHApp : forall s : Comp, P s -> forall t : Comp, P t -> P (s t)) (IHClos : forall (s : term) (A : list Comp), (forall a, a el A -> P a) -> P (CompClos s A)) : forall x, P x.
Proof.
apply Comp_ind_deep' with (Pl:=fun A => (forall a, a el A -> P a));auto.
intros.
inv H1;auto.
Fixpoint substList (s:term) (x:nat) (A: list term): term := match s with | var n => if Dec (x>n) then var n else nth (n-x) A (var n) | app s t => app (substList s x A) (substList t x A) | lam s => lam (substList s (S x) A) end.
Fixpoint deClos (s:Comp) : term := match s with | CompVar x => var x | CompApp s t => app (deClos s) (deClos t) | CompClos s A => substList s 0 (map deClos A) end.
Reserved Notation "s '>[(' l ')]' t" (at level 50, format "s '>[(' l ')]' t").
Declare Scope LClos.
Inductive CPow : nat -> Comp -> Comp -> Prop := | CPowRefl (s:Comp) : s >[(0)] s | CPowTrans (s t u:Comp) i j : s >[(i)] t -> t >[(j)] u -> s >[(i+j)] u | CPowAppL (s s' t :Comp) l: s >[(l)] s' -> (s t) >[(l)] (s' t) | CPowAppR (s t t':Comp) l: t >[(l)] t' -> (s t) >[(l)] (s t') | CPowApp (s t:term) (A:list Comp) : CompClos (app s t) A >[(0)] (CompClos s A) (CompClos t A) | CPowVar (x:nat) (A:list Comp): CompClos (var x) A >[(0)] nth x A (CompVar x) | CPowVal (s t:term) (A B:list Comp): lambda t -> (CompClos (lam s) A) (CompClos t B) >[(1)] (CompClos s ((CompClos t B)::A)) where "s '>[(' l ')]' t" := (CPow l s t) : LClos.
Open Scope LClos.
Ltac inv_CompStep := match goal with | H : (CompApp _ _) >(_) CompClos _ _ |- _ => inv H | H : (CompClos _ _) >(_) CompApp _ _ |- _ => inv H end.
Hint Constructors CPow : core.
Instance CPow'_App_properR n: Proper (eq ==> (CPow n) ==> (CPow n)) CompApp.
Proof.
intros ? ? -> ? ? ?.
now eapply CPow_congR.
Hint Resolve deClos_validEnv : core.
Hint Resolve validComp_step : core.

Instance CPow'_App_properR n: Proper (eq ==> (CPow n) ==> (CPow n)) CompApp.
Proof.
intros ? ? -> ? ? ?.
now eapply CPow_congR.

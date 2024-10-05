From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LFinType LBool LProd Lists.
From Undecidability.L.Functions Require Import EqBool.
Set Default Proof Using "Type".
Section Lookup.
Variable X Y : Type.
Context {eqbX : X -> X -> bool}.
Context `{eqbClass X eqbX}.
Fixpoint lookup (x:X) (A:list (X*Y)) d: Y := match A with [] => d | (key,Lproc)::A => if eqb x key then Lproc else lookup x A d end.
Context `{registered X} `{@eqbCompT X _ eqbX _}.
Definition lookupTime (x:nat) (l:list (X*Y)):= fold_right (fun '(a,b) res => eqbTime (X:=X) x (size (enc (a:X))) + res +24) 4 l.
Global Instance term_lookup `{registered Y}: computableTime' (lookup) (fun x _ => (5, fun l _ => (1, fun d _ => (lookupTime (size (enc x)) l,tt)))).
Proof.
unfold lookup.
unfold eqb.
extract.
unfold lookupTime.
solverec.
End Lookup.
Section funTable.
Variable X : finType.
Variable Y : Type.
Variable f : X -> Y.
Definition funTable := map (fun x => (x,f x)) (elem X).
Variable (eqbX : X -> X -> bool).
Context `{eqbClass X eqbX}.
End funTable.
Section finFun.
Context (X : finType) Y {reg__X:registered X} {reg__Y:registered Y}.
Context {eqbX : X -> X -> bool} `{eqbClass X eqbX} `{H0 : @eqbCompT X _ eqbX _}.
End finFun.

Lemma lookup_sound' (A: Type) (B: Type) eqbA `{eqbClass (X:=A) eqbA} (L : list (prod A B)) a b def : (forall a' b1 b2, (a',b1) el L -> (a',b2) el L -> b1=b2) -> ( (a,b) el L \/ ((forall b', ~ (a,b') el L) /\ b = def) ) -> lookup a L def = b.
Proof.
intros H1 H2.
induction L as [ |[a' b'] L].
now intuition.
cbn.
destruct (eqb_spec a a').
-
subst a.
destruct H2.
2:now exfalso.
eapply H1.
all:easy.
-
apply IHL.
all:intros.
+
eapply H1.
all:eauto.
+
destruct H2 as [[]|].
all:easy.

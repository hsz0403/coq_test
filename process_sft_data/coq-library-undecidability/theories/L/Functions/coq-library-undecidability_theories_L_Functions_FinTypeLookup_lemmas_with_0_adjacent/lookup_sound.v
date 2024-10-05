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

Lemma lookup_sound (A: Type) (B: Type) eqbA `{eqbClass (X:=A) eqbA} (L : list (A * B)) a b def : (forall a' b1 b2, (a', b1) el L -> (a', b2) el L -> b1 = b2) -> (a, b) el L -> lookup a L def = b.
Proof.
intros H1 H2.
induction L; cbn; [ destruct H2 | ].
destruct a0 as [a0 b0].
specialize (H a a0) as Heqb.
apply reflect_iff in Heqb.
unfold EqBool.eqb.
destruct eqbA.
-
specialize (proj2 Heqb eq_refl) as ->.
destruct H2 as [H2 | H2]; [easy | ].
apply (H1 a0); easy.
-
assert (not (a = a0)).
{
intros ->.
easy.
}
destruct H2 as [H2 | H2]; [ congruence | ].
apply IHL in H2; [easy | intros; now eapply H1].

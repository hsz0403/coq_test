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

Lemma finFun_computableTime_const (f:X -> Y) (d:Y): {c & computableTime' f (fun _ _ => (c,tt))}.
Proof using H0.
evar (c:nat).
exists c.
apply computableTimeExt with (x:= (fun c => lookup c (funTable f) d )).
{
cbn.
intros ?.
now rewrite lookup_funTable.
}
extract.
solverec.
rewrite lookupTime_leq.
unfold funTable.
rewrite map_length,size_finType_any_le.
unfold c.
reflexivity.

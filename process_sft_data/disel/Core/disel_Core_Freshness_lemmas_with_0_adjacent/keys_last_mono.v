From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Section Keys.
Variables (K : ordType) (V : Type) (U : union_map_class K V).
Implicit Types (k : K) (v : V) (f : U).
End Keys.
Section FreshLastKey.
Variable V : Type.
Implicit Type f : union_map [ordType of nat] V.
Definition last_key f := last 0 (dom f).
Definition fresh f := (last_key f).+1.
End FreshLastKey.

Lemma keys_last_mono f1 f2 k : path oleq k (dom f1) -> path oleq k (dom f2) -> (forall x, x \in dom f1 -> x \in dom f2) -> oleq (last k (dom f1)) (last k (dom f2)).
Proof.
rewrite !umEX; case: (UMC.from f1); first by move=>_ H _; apply: path_last H.
move=>{f1} f1 /= _ H1; case: (UMC.from f2)=>/=.
-
by move=>_ /allP; case: (supp f1)=>//; rewrite /oleq eq_refl orbT.
by move=>{f2} f2 /= _; apply: seq_last_mono H1.

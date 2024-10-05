From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import axioms pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Actions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Injection.
Section Injection.
Variable W : world.
Structure injects (U V : world) (K : hooks) := Inject { (* The "delta world" *) E : world; _ : hook_complete U /\ hook_complete E; (* Additional hooks are included with an empty world *) _ : V = U \+ E \+ (Unit, K); (* Additional hooks are well-formed with respect to the world *) _ : hooks_consistent (getc (U \+ E)) K; (* These all should be easy to prove given a standard world disentanglement *) _ : forall s, Coh V s <-> exists s1 s2, [/\ s = s1 \+ s2, Coh U s1 & Coh E s2]; (* Framing wrt. worlds and hooks *) _ : forall s1 s2 s this, s1 \+ s \In Coh V -> network_step U this s1 s2 -> network_step V this (s1 \+ s) (s2 \+ s); _ : forall s1 s2 s1' s2' this, s1 \In Coh U -> s2 \In Coh U -> network_step V this (s1 \+ s1') (s2 \+ s2') -> (network_step U this s1 s2 /\ s1' = s2') \/ (network_step E this s1' s2' /\ s1 = s2); }.
End Injection.
Module Exports.
Section Exports.
Definition inj_ext := E.
Definition injects := injects.
Definition Inject := Inject.
Definition extends (U V : world) (K : hooks) (w : injects U V K) s s1 := exists s2, [/\ s = s1 \+ s2, s1 \In Coh U & s \In Coh V].
Notation dom_filt W := (fun k => k \in dom W).
Definition projectS (W : world) (s : state) := um_filter (dom_filt (getc W)) s.
End Exports.
End Exports.
End Injection.
Export Injection.Exports.
Module InjectExtra.
Definition not_hooked_by (K : hooks) l := forall z lc l' st, (z, lc, (l', st)) \in dom K -> l != l'.
Definition world_not_hooked (W: world) K := forall l, l \in dom W.1 -> not_hooked_by K l.
End InjectExtra.
Export InjectExtra.

Lemma projectSE W1 W2 s : s \In Coh (W1 \+ W2) -> s = projectS W1 s \+ projectS W2 s.
Proof.
case=>Vw Vs G D H; rewrite /projectS.
have X: {in dom s, dom_filt (getc W2) =1 predD (dom_filt (getc W2)) (dom_filt (getc W1))}.
-
move=>z _/=; case I : (z \in dom (W1.1 \+ W2.1)).
+
move: I; rewrite domUn !inE/==>/andP[V']/orP[]Z; rewrite Z/=.
-
by case: validUn V'=>//_ _/(_ z Z)/=G' _;apply/negbTE.
rewrite joinC in V'; case: validUn V'=>//_ _/(_ z Z)G' _.
by rewrite andbC.
move: I; rewrite domUn inE/==>/negbT; rewrite negb_and negb_or/=.
have X: valid (W1 \+ W2) by [].
by case/andP: X=>->/=_/andP[]->.
rewrite (eq_in_umfilt X) -umfilt_predU/=; clear X.
suff X: {in dom s, predU (dom_filt (getc W1)) (dom_filt (getc W2)) =1 predT}.
-
by rewrite (eq_in_umfilt X) umfilt_predT.
by move=>z; rewrite/= -D domUn inE=>/andP[].

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

Lemma cohUnKR U W s s': s \+ s' \In Coh (U \+ W) -> s \In Coh U -> hook_complete W -> s' \In Coh W.
Proof.
move=>H C G2; move: (cohH C) => G1.
suff X: s' = projectS W (s \+ s').
-
by rewrite X; apply: (projectS_cohR H).
suff X: s = projectS U (s \+ s').
-
move: (cohS H)=>V; move/projectSE: (H)=>E.
rewrite E in V.
rewrite {1}X in E.
by rewrite (joinxK V (sym_eq E)).
rewrite /projectS.
suff X: {in dom (s \+ s'), dom U.1 =i dom s}.
-
by rewrite (eq_in_umfilt X) umfilt_dom ?(cohS H)//.
by move=>z _; move: (cohD C z); rewrite /in_mem.

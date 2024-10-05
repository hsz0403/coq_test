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

Lemma hooks_frame (U W : world) (K : hooks) l st s s' n msg to : hook_complete U -> hook_complete W -> hooks_consistent (U \+ W).1 K -> l \in dom s -> s \In Coh U -> s \+ s' \In Coh (U \+ W \+ (Unit, K)) -> not_hooked_by K l -> all_hooks_fire (geth U) l st s n msg to -> all_hooks_fire (geth (U \+ W \+ (Unit, K))) l st (s \+ s') n msg to.
Proof.
move=>G1 G2 G D' C1 C' N A z lc hk F D1 D2; move: F.
case/andP: (cohW C')=>/=V1 V2.
move: (cohUnKR (coh_hooks C') C1 G2) => C2.
rewrite findUnL ?V2//=; case: ifP=>D3; last first.
-
move => F; apply sym_eq in F; move: F.
by move/find_some/N/negP; rewrite eqxx.
rewrite findUnR ?(validL V2)//; case: ifP=>[D|_].
+
case/G2/andP: D=>_ D; rewrite (cohD C2) in D.
by case: validUn (cohS C')=>//_ _/(_ _ D'); rewrite D.
move => F.
apply sym_eq in F.
have D'': lc \in dom s by case/andP:(G1 _ _ _ _ (find_some F)); rewrite (cohD C1).
have E: getStatelet s l = getStatelet (s \+ s') l by rewrite (getSUn (cohS C'))// -?(cohD C1').
have E': getStatelet s lc = getStatelet (s \+ s') lc.
by rewrite (getSUn (cohS C'))// -?(cohD C1').
move: (getStatelet (s \+ s') l) (getStatelet (s \+ s') lc) E E'.
by move=>y1 y2 Z1 Z2; subst y1 y2; apply sym_eq in F; apply: (A z).

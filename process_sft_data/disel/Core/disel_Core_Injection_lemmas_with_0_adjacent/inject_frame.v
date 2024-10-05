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

Lemma inject_frame U W K this s1 s2 s: s1 \+ s \In Coh (U \+ W \+ (Unit, K)) -> network_step U this s1 s2 -> hook_complete U -> hook_complete W -> hooks_consistent (U \+ W).1 K -> (* State something about hook direction *) world_not_hooked U K -> network_step (U \+ W \+ (Unit, K)) this (s1 \+ s) (s2 \+ s).
Proof.
move=>C1 S Ku Kw Hk N; move/step_coh: (S)=>[C1' C2'].
case: S; first by move=>[_ <-]; apply: Idle.
-
move=>l st H1 to msg h H2 H3 _ S A H4 G.
have E: getProtocol U l = getProtocol (U \+ W \+ (Unit, K)) l.
have Y: getProtocol U l = getProtocol (U \+ W) l.
+
by rewrite (getPUn (validL (cohW C1)))// (cohD C1').
rewrite Y; rewrite (getPUn (cohW C1))// domUn inE (cohD C1') H3/=.
by case/andP: (validL (cohW C1))=>->.
have E': getStatelet s1 l = getStatelet (s1 \+ s) l.
by rewrite (getSUn (cohS C1))// -?(cohD C1').
have X: l \in dom (s1 \+ s) by rewrite domUn inE H3 (cohS C1).
move: (getProtocol U) (E) H2=>_ -> H2.
rewrite /get_st /InMem/= in H1.
rewrite E' in H2 G S H4; clear E'.
move: (getProtocol U l) E st H1 S H4 G H2 A=>_->st H1 S H4 G H2 A.
apply: (SendMsg H1 H2 X C1 _ H4 (s2 := s2 \+ s)); last first.
-
by rewrite updUnL H3; congr (_ \+ _).
by apply: hooks_frame=>//; apply: N; rewrite -(cohD C1') in H3.
move=> l rt H1 msg from H2 H3 C tms G [G1 G2/= G3].
have E: getProtocol U l = getProtocol (U \+ W \+ (Unit, K)) l.
have Y: getProtocol U l = getProtocol (U \+ W) l.
-
by rewrite (getPUn (validL (cohW C1)))// (cohD C1').
rewrite Y; rewrite (getPUn (cohW C1))// domUn inE (cohD C1') H3/=.
by case/andP: (validL (cohW C1))=>->.
have E': getStatelet s1 l = getStatelet (s1 \+ s) l.
by rewrite (getSUn (cohS C1))// -?(cohD C1').
have X: l \in dom (s1 \+ s) by rewrite domUn inE (cohS C1) H3.
rewrite /get_rt /InMem /= in H1.
move: (getProtocol U l) (getStatelet s1 l) E E' C H2 (coh_s l C) rt G3 G G2 H1 G1=>z1 z2 Z1 Z2.
subst z1 z2=>C pf C' G3 G G2 H1 H2 G1.
apply: (ReceiveMsg H2 X G2 (i := msg) (from := from) (s2 := s2 \+ s)).
split=>//=; first by rewrite (pf_irr (coh_s l C1) C').
rewrite updUnL H3; congr (_ \+ _); move: (NetworkSem.coh_s l C1)=>pf'.
by rewrite (pf_irr pf' C').

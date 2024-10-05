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

Lemma inject_step U W K this s1 s2 s1' s2' : valid (U \+ W) -> s1 \In Coh U -> s2 \In Coh U -> hook_complete U -> hook_complete W -> network_step (U \+ W \+ (Unit, K)) this (s1 \+ s1') (s2 \+ s2') -> network_step U this s1 s2 /\ s1' = s2' \/ network_step W this s1' s2' /\ s1 = s2.
Proof.
move=>V C1 C2 Hu Hw S; move/step_coh: (S)=>[C1' C2'].
move: (cohW C1')=>V1.
move: (coh_hooks C1')(coh_hooks C2')=>{C1'}C1'{C2'}C2'.
move: (cohUnKR C1' C1 Hw) (cohUnKR C2' C2 Hw)=>D1 D2.
case: S; first 2 last.
move=>l rt R i from H1.
rewrite domUn inE=>/andP[Vs]/=/orP; case=>D C msg H2 [H3 H4]/=; [rewrite updUnL D|rewrite updUnR D]=>G;[left|right].
-
have X: s1' = s2'.
+
move: (C2'); rewrite (joinC U) G -[upd _ _ _ \+ s1'](joinC s1').
move/cohUnKR/(_ D1)/(_ Hu)=>C1''.
move: (coh_prec (cohS C2') C2 C1'' G)=>Z; rewrite -Z in G; clear Z.
by rewrite (joinxK (cohS C2') G).
split=>//; subst s2'; rewrite -![_ \+ s1'](joinC s1') in G C2'.
rewrite -[upd _ _ _ \+ s1'](joinC s1') in G; rewrite (joinC U) in C2'.
move: (joinxK (cohS C2') G)=>{G}G.
have E: getProtocol U l = getProtocol (U \+ W) l.
by rewrite (getPUn V)// (cohD C1).
have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
by rewrite (getSUn (cohS C1')).
rewrite /get_rt /InMem/= in R.
move: (getStatelet (s1 \+ s1') l) E' C (coh_s l C) H1 G H3 H4=>_<-_.
move: (getProtocol (U \+ W \+ (Unit, K)) l) (get_protocol_hooks K l V) E rt R H2=>_-><-rt R H2 coh_s H1 G H3 H4.
apply: (ReceiveMsg R D H2 (i := i) (from := from) (s2 := s2) (C := C1)).
split=>//=; move: (NetworkSem.coh_s l C1)=>coh_s'; by rewrite -(pf_irr coh_s coh_s').
move: U W V {V1} Hw Hu s1 s2 s1' s2' C1 C2 C1' C2' D1 D2 rt H1 H2 Vs D C R H3 H4 G.
move=>W U V Hw Hu s1' s2' s1 s2 D1 D2.
rewrite !(joinC W) -!(joinC s1) -!(joinC s2)=> C1' C2' C1 C2.
move=>rt H1 H2 Vs D C R H3 H4 G.
have X: s1' = s2'.
-
move: (C2'); rewrite (joinC U) G.
move/cohUnKR/(_ D1)/(_ Hw)=>C1''; rewrite (joinC s1') in G.
move: (coh_prec (cohS C2') C2 C1'' G)=>Z; rewrite -Z in G; clear Z.
by rewrite (joinxK (cohS C2') G).
split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
rewrite (joinC U) in C2'; move: (joinxK (cohS C2') G)=>{G}G.
rewrite joinC in V.
have E: getProtocol U l = getProtocol (U \+ W) l.
by rewrite (getPUn V)// (cohD C1).
have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
by rewrite (getSUn (cohS C1')).
rewrite /get_rt /InMem/= in R.
move: (getStatelet (s1 \+ s1') l) E' C (coh_s l C) H1 G H3 H4=>_<-_.
move: (getProtocol (U \+ W \+ (Unit, K)) l) (get_protocol_hooks K l V) E rt R H2=>_-><-rt R H2 coh_s H1 G H3 H4.
apply: (ReceiveMsg R D H2 (i := i) (from := from) (s2 := s2) (C := C1)).
split=>//=; move: (NetworkSem.coh_s l C1)=>coh_s'; by rewrite -(pf_irr coh_s coh_s').
-
case=>_ E; move: (coh_prec (cohS C1') C1 C2 E)=>Z; subst s2.
rewrite (joinC U) (joinC s1) in C1'; rewrite !(joinC s1) in E.
move: (coh_prec (cohS C1') D1 D2 E)=>Z; subst s2'.
by left; split=>//; apply: Idle.
-
move=>l st H1 to msg h H2.
rewrite domUn inE=>/andP[Vs]/orP; case=> D _ S Hk H3; [rewrite updUnL D|rewrite updUnR D]=>G;[left|right]; [| move: U W V1 Hu Hw V s1 s2 s1' s2' C1 C2 C1' C2' D1 D2 st Hk H1 H2 Vs D S H3 G; move=> W U V1 Hw Hu V s1' s2' s1 s2 D1 D2 C1' C2' C1 C2 st Hk H1 H2 Vs D S H3 G; rewrite (joinC W) in V C1' C2' st H1 S H3 G H2 Hk; rewrite -?(joinC s1) -?(joinC s2) in C1' C2' S G H3 Vs].
+
have X: s1' = s2'.
-
move: (C2'); rewrite (joinC U) G -[upd _ _ _ \+ s1'](joinC s1').
move/cohUnKR/(_ D1)/(_ Hu)=>C1''.
move: (coh_prec (cohS C2') C2 C1'' G)=>Z; rewrite -Z in G; clear Z.
by rewrite (joinxK (cohS C2') G).
split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
rewrite (joinC U) in C2'; move: (joinxK (cohS C2') G)=>{G}G.
rewrite (joinC s1') in G.
have E: getProtocol U l = getProtocol (U \+ W) l.
by rewrite (getPUn V)// (cohD C1).
have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
by rewrite (getSUn Vs).
rewrite /get_st /InMem in H1.
move: (getStatelet (s1 \+ s1') l) (E') H2 S H3 G=>_<- H2 S H3 G.
move: (getProtocol (U \+ W \+ (Unit, K)) l) (get_protocol_hooks K l V) E st H1 S H2 H3 G Hk=>_-><- st H1 S H2 H3 G Hk.
apply: (SendMsg H1 H2 D C1 _ H3 G).
move=>z lc hk F A1 A2.
apply sym_eq in F.
move: (Hk z lc hk).
rewrite -F -joinA !domUn !inE !Vs A1 A2 findUnL ?E' ?(find_some F)/=; last by case/andP:V1; rewrite-joinA =>_->.
move/(_ erefl is_true_true is_true_true).
by rewrite {1 3}/getStatelet findUnL// A1.
have X: s1' = s2'.
-
move: (C2'); rewrite (joinC U) G.
move/cohUnKR/(_ D1)/(_ Hu)=>C1''; rewrite (joinC s1') in G.
move: (coh_prec (cohS C2') C2 C1'' G)=>Z; rewrite -Z in G; clear Z.
by rewrite (joinxK (cohS C2') G).
split=>//; subst s2'; rewrite -!(joinC s1') in G C2'.
rewrite (joinC U) in C2'; move: (joinxK (cohS C2') G)=>{G}G.
rewrite (joinC s1') in G.
have E: getProtocol U l = getProtocol (U \+ W) l.
by rewrite (getPUn V)// (cohD C1).
have E': getStatelet s1 l = getStatelet (s1 \+ s1') l.
by rewrite (getSUn Vs).
rewrite /get_st /InMem in H1; rewrite (joinC s1') in H2.
move: (getStatelet (s1 \+ s1') l) (E') H2 S H3 G=>_<- H2 S H3 G.
move: (getProtocol (U \+ W \+ (Unit, K)) l) (get_protocol_hooks K l V) E st H1 S H2 H3 G Hk=>_-><- st H1 S H2 H3 G Hk.
apply: (SendMsg H1 H2 D C1 _ H3 G).
move=>z lc hk F A1 A2.
apply sym_eq in F.
move: (Hk z lc hk).
rewrite -F -joinA !domUn !inE A1 A2 findUnL ?E' ?(find_some F)/=; last by rewrite joinA (joinC U.2); case/andP:V1=>_->.
rewrite !(joinC s1') !Vs/= -!(orbC true).
move/(_ erefl is_true_true is_true_true).
by rewrite {1 3}/getStatelet findUnL// A1.

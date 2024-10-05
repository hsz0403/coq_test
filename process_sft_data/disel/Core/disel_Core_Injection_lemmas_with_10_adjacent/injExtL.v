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

Lemma cohK (U V : world) (K : hooks) (w : injects U V K) : V = U \+ inj_ext w \+ (Unit, K).
Proof.
Admitted.

Lemma cohE (U V : world) (K : hooks) (w : injects U V K) s : Coh V s <-> exists s1 s2, [/\ s = s1 \+ s2, Coh U s1 & Coh (inj_ext w) s2].
Proof.
Admitted.

Lemma sem_extend (U V : world) (K : hooks) (w : injects U V K) s1 s2 s this: s1 \+ s \In Coh V -> s2 \+ s \In Coh V -> network_step U this s1 s2 -> network_step V this (s1 \+ s) (s2 \+ s).
Proof.
Admitted.

Lemma sem_split (U V : world) (K : hooks) (w : injects U V K) s1 s1' s2 s2' this: s1 \In Coh U -> s2 \In Coh U -> network_step V this (s1 \+ s1') (s2 \+ s2') -> (network_step U this s1 s2 /\ s1' = s2') \/ (network_step (inj_ext w) this s1' s2' /\ s1 = s2).
Proof.
Admitted.

Lemma projectS_cohL W1 W2 s : s \In Coh (W1 \+ W2) -> hook_complete W1 -> projectS W1 s \In Coh W1.
Proof.
case=>V1 V2 G1 D H G2; split=>//; first by move/validL: V1.
-
by rewrite valid_umfilt.
-
move=>z; case B: (z \in dom (getc W1)).
+
by rewrite dom_umfilt !inE B/= -D/=domUn !inE B/=; case/andP:V1=>->.
by rewrite dom_umfilt !inE B.
move=>l; move: (H l)=>{H}H.
case B: (l \in dom (getc W1)); last first.
-
rewrite /getProtocol /getStatelet; move: (B).
case: dom_find=>//-> _.
suff X: ~~(l \in dom (projectS W1 s)) by case: dom_find X=>//-> _.
by rewrite /projectS dom_umfilt inE/= B.
have E1: find l s = find l (projectS W1 s).
-
by rewrite /projectS/= find_umfilt B.
have E2: getProtocol (W1 \+ W2) l = getProtocol W1 l.
-
rewrite /getProtocol findUnL//?B//.
by rewrite /valid/= in V1; case/andP: V1.
Admitted.

Lemma projectS_cohR W1 W2 s : s \In Coh (W1 \+ W2) -> hook_complete W2 -> projectS W2 s \In Coh W2.
Proof.
Admitted.

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
Admitted.

Lemma coh_split W1 W2 s : s \In Coh (W1 \+ W2) -> hook_complete W1 -> hook_complete W2 -> exists s1 s2 : state, [/\ s1 \In Coh W1, s2 \In Coh W2 & s = s1 \+ s2].
Proof.
move=>C G1 G2; move/projectSE: (C)->.
exists (projectS W1 s), (projectS W2 s).
Admitted.

Lemma injExtL' (W1 W2 : world) K (pf : injects W1 (W1 \+ W2) K) : valid (W1 \+ W2) -> inj_ext pf \+ (Unit, K) = W2.
Proof.
move=>H; case: pf=>W2' _ E/=_ _ _ _.
rewrite -joinA in E.
case/andP: H=>H1 H2.
rewrite /PCM.join/= in H1 H2 E *.
case: W2 H1 H2 E=>/=c2 h2 H1 H2 [E1 E2].
Admitted.

Lemma injExtR' W1 W2 K (pf : injects W2 (W1 \+ W2) K) : valid (W1 \+ W2) -> inj_ext pf \+ (Unit, K) = W1.
Proof.
move=>H; case: pf=>W2' _ E/= _ _ _ _.
rewrite -(joinC W2) in E H.
case/andP: H=>H1 H2; rewrite -joinA in E.
rewrite /PCM.join/= in H1 H2 E *.
case: W1 H1 H2 E=>/=c1 h1 H1 H2 [E1 E2].
Admitted.

Lemma injExtR W1 W2 (pf : injects W2 (W1 \+ W2) Unit) : valid (W1 \+ W2) -> inj_ext pf = W1.
Proof.
Admitted.

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
Admitted.

Lemma cohUnKL U W s s': s \+ s' \In Coh (U \+ W) -> s' \In Coh W -> hook_complete U -> s \In Coh U .
Proof.
Admitted.

Lemma getPUn (U W : world) l : valid (U \+ W) -> l \in dom U.1 -> getProtocol U l = getProtocol (U \+ W) l.
Proof.
move=>V; rewrite /getProtocol=>D.
case/andP: (V)=>V1 V2.
Admitted.

Lemma getSUn s1 s2 l : valid (s1 \+ s2) -> l \in dom s1 -> getStatelet s1 l = getStatelet (s1 \+ s2) l.
Proof.
move=>V; rewrite /getStatelet=>D.
Admitted.

Lemma hook_completeL (U : world) K : valid (U \+ (Unit, K)) -> hook_complete (U \+ (Unit, K)) -> hook_complete U.
Proof.
case: U=>c h=> V H z lc ls st D.
move: (H z lc ls st); rewrite domUn inE/= D/=.
case/andP: V=>_->/==>/(_ is_true_true)=>/andP[].
Admitted.

Lemma get_protocol_hooks (U: world) K l: valid U -> getProtocol (U \+ (Unit, K)) l = getProtocol U l.
Proof.
move=>V; rewrite /getProtocol.
Admitted.

Lemma coh_hooks (U : world) K s : s \In (Coh (U \+ (Unit, K))) -> s \In (Coh U).
Proof.
case=>V Vs Hk D L.
split=>//; first by move/validL: V.
-
by apply: hook_completeL V Hk.
-
move=>z; rewrite -D domUn !inE/= unitR dom0 orbC/=.
by move/validL:V=>/andP[]->_.
Admitted.

Lemma inj_hooks_complete (U W : world) K: valid (U \+ W \+ (Unit, K)) -> hook_complete U -> hook_complete W -> hooks_consistent (U \+ W).1 K -> hook_complete (U \+ W \+ (Unit, K)).
Proof.
move=>V G1 G2 G.
move=>z lc ls st; rewrite domUn !inE/= !unitR.
move/andP: (V)=>[_]->/=; case/orP; last by move/G.
rewrite !domUn !inE; case/validL/andP:V=>->->/=.
case/orP; first by case/G1/andP=>->->.
Admitted.

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
Admitted.

Lemma injExtL W1 W2 (pf : injects W1 (W1 \+ W2) Unit) : valid (W1 \+ W2) -> inj_ext pf = W2.
Proof.
by move/(injExtL' pf); rewrite unitR.

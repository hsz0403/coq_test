From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
From DiSeL Require Import NewStatePredicates.
From DiSeL Require Import SeqLib.
From DiSeL Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL Require Import TwoPhaseProtocol TwoPhaseCoordinator TwoPhaseParticipant.
From DiSeL Require TwoPhaseInductiveProof.
From DiSeL Require Import QueryProtocol QueryHooked.
Section QueryPlusTPC.
Variables (lc lq : Label).
Variables (cn : nid) (pts : seq nid).
Hypothesis Lab_neq: lq != lc.
Hypothesis Hnin : cn \notin pts.
Hypothesis Puniq : uniq pts.
Hypothesis PtsNonEmpty : pts != [::].
Definition pc : protocol := TwoPhaseInductiveProof.tpc_with_inv lc [::] Hnin.
Definition Data : Type := (nat * Log).
Definition qnodes := cn :: pts.
Variable serialize : Data -> seq nat.
Variable deserialize : seq nat -> Data.
Hypothesis ds_inverse : left_inverse serialize deserialize.
Definition local_indicator (d : Data) := [Pred h | h = st :-> (d.1, CInit) \+ log :-> d.2].
Definition core_state_to_data n h (d : Data) := if n == cn then h = st :-> (d.1, CInit) \+ log :-> d.2 else h = st :-> (d.1, PInit) \+ log :-> d.2.
Notation getLc s n := (getLocal n (getStatelet s lc)).
Notation cn_agree := TwoPhaseInductiveInv.cn_log_agreement.
Definition W := QueryHooked.W lq pc Data qnodes serialize core_state_to_data.
Notation loc_qry s := (getLocal cn (getStatelet s lq)).
Notation loc_tpc' s n := (getLocal n (getStatelet s lc)).
Notation loc_tpc s := (loc_tpc' s cn).
Notation qry_init := (query_init_state lq Data qnodes serialize cn).
Definition cn_request_log := request_data_program _ pc _ _ _ _ ds_inverse _ core_state_to_data_inj Lab_neq _ cn_in_qnodes local_indicator core_state_stable_step (0, [::]).
Definition coordinator ds := with_inv (TwoPhaseInductiveProof.ii _ _ _) (coordinator_loop_zero lc cn pts [::] Hnin Puniq PtsNonEmpty ds).
Program Definition coordinate_and_query (ds : seq data) to : {rr : seq (nid * nat) * seq (nid * nat)}, DHT [cn, W] (fun i => let: (reqs, resp) := rr in [/\ loc_tpc i = st :-> (0, CInit) \+ log :-> ([::] : seq (bool * data)), to \in qnodes, loc_qry i = qst :-> (reqs, resp) & qry_init to i], fun (res : Data) m => let: (reqs, resp) := rr in exists (chs : seq bool), let: d := (size ds, seq.zip chs ds) in [/\ loc_tpc m = st :-> (d.1, CInit) \+ log :-> d.2, loc_qry m = qst :-> (reqs, resp), qry_init to m & res = d]) := Do _ ( iinject (coordinator ds);; cn_request_log to).
Next Obligation.
by exact : (query_hookz lq pc Data qnodes serialize core_state_to_data).
Defined.
Next Obligation.
exact: (injW lq pc Data qnodes serialize core_state_to_data Lab_neq).
Defined.
Next Obligation.
apply:ghC=>i0[rq rs][P1 P2 P3 P4]C0; apply: step.
move: (C0)=>CD0; rewrite /W eqW in CD0; move: (coh_hooks CD0)=>{CD0}CD0.
case: (coh_split CD0); try apply: hook_complete0.
move=>i1[j1][C1 D1 Z].
subst i0; apply: inject_rule=>//.
have E : loc_tpc (i1 \+ j1) = loc_tpc i1 by rewrite (locProjL CD0 _ C1)// domPt inE andbC eqxx.
rewrite E{E} in P1.
apply: with_inv_rule'.
apply: call_rule=>//_ i2 [chs]L2 C2 Inv j2 CD2/= R.
have E : loc_qry (i1 \+ j1) = loc_qry j1 by rewrite (locProjR CD0 _ D1)// domPt inE andbC eqxx.
rewrite E {E} -(rely_loc' _ R) in P3.
case: (rely_coh R)=>_ D2.
rewrite /W eqW in CD2; move: (coh_hooks CD2)=>{CD2}CD2.
rewrite /mkWorld/= in C2.
have C2': i2 \In Coh (plab pc \\-> pc, Unit).
-
split=>//=.
+
by rewrite /valid/= valid_unit validPt.
+
by apply: (cohS C2).
+
by apply: hook_complete0.
+
by move=>z; rewrite -(cohD C2) !domPt.
move=>l; case B: (lc == l).
+
move/eqP:B=>B; subst l; rewrite /getProtocol findPt; split=>//.
by move: (coh_coh lc C2); rewrite /getProtocol findPt.
have X: l \notin dom i2 by rewrite -(cohD C2) domPt inE; move/negbT: B.
rewrite /getProtocol/= (find_empty _ _ X).
have Y: l \notin dom (lc \\-> pc) by rewrite domPt inE; move/negbT: B.
by case: dom_find Y=>//->_.
have D2': j2 \In Coh (lq \\-> pq lq Data qnodes serialize, Unit) by apply: (cohUnKR CD2 _); try apply: hook_complete0.
rewrite -(locProjL CD2 _ C2') in L2; last by rewrite domPt inE eqxx.
rewrite -(locProjR CD2 _ D2') in P3; last by rewrite domPt inE eqxx.
clear C2 D2.
rewrite injWQ in R.
rewrite /query_init_state/= in P4.
rewrite (locProjR CD0 _ D1) in P4; last by rewrite domPt inE eqxx.
have Q4: qry_init to j2.
-
by apply: (query_init_rely' lq Data qnodes serialize cn to _ _ P4 R).
clear P4.
rewrite /query_init_state/= -(locProjR CD2 _ D2') in Q4; last by rewrite domPt inE eqxx.
apply (gh_ex (g:=(rq, rs, (size ds, seq.zip chs ds)))).
apply: call_rule=>//=; last by move=>d m[->->T1 T2->]_; eexists _.
move=>CD2'; split=>//.
case/orP: P2=>[|P]; first by move/eqP=>Z; subst to; rewrite /core_state_to_data eqxx.
rewrite !(locProjL CD2 _ C2') in L2 *; last by rewrite domPt inE eqxx.
move: (coh_coh lc C2'); rewrite prEq; case=>C3 _.
rewrite /core_state_to_data; case:ifP=>//[|_]; first by move=>/eqP Z; subst to.
by apply: (@cn_agree lc cn pts [::] Hnin _ _ _ to C3 _ Inv).
End QueryPlusTPC.

Lemma loc_imp_core s d n : Coh W s -> n \in qnodes -> local_indicator d (loc_tpc s) -> core_state_to_data n (loc_tpc' s n) d.
Proof.
move=>C Nq E.
case/orP: Nq=>[|P]; first by move/eqP=>z; subst n; rewrite /core_state_to_data eqxx.
case: (C)=>_ _ _ _/(_ lc); rewrite prEqC//=; case=> C2 Inv.
move: (@cn_agree lc cn pts [::] Hnin (getStatelet s lc) d.1 d.2 n C2 E Inv P)=>->.
rewrite /core_state_to_data; case:ifP=>//.
move=>/eqP Z; subst n; move/negbTE: Hnin=>Z.
suff X: cn \in pts by rewrite X in Z.
done.

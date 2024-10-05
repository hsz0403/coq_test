From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import State Protocols Worlds NetworkSem Rely.
From DiSeL Require Import HoareTriples InferenceRules While.
From DiSeL Require Import TwoPhaseProtocol TwoPhaseCoordinator TwoPhaseParticipant.
From DiSeL Require TwoPhaseInductiveProof.
Section SimpleTpcApp.
Definition l := 0.
Definition cn := 0.
Definition p1 := 1.
Definition p2 := 2.
Definition p3 := 3.
Definition pts := [::p1; p2; p3].
Definition others : seq nid := [::].
Fact Hnin : cn \notin pts.
Proof.
by [].
Fact PtsNonEmpty : pts != [::].
Proof.
by [].
Fact Puniq : uniq pts.
Proof.
by [].
Variable data_stream : seq data.
Definition coordinator := coordinator_loop_zero l cn pts others Hnin Puniq PtsNonEmpty data_stream.
Program Definition participant p (pf : p \in pts) choices := participant_with_choices l cn pts others Hnin p pf choices.
Variables (choices1 choices2 choices3 : seq bool).
Definition st_ptr := TPCProtocol.States.st.
Definition log_ptr := TPCProtocol.States.log.
Definition init_heap_c := st_ptr :-> (0, CInit) \+ log_ptr :-> ([::] : seq (bool * data)).
Definition init_heap_p := st_ptr :-> (0, PInit) \+ log_ptr :-> ([::] : seq (bool * data)).
Definition init_dstate := cn \\-> init_heap_c \+ p1 \\-> init_heap_p \+ p2 \\-> init_heap_p \+ p3 \\-> init_heap_p.
Notation init_dstatelet := (DStatelet init_dstate Unit).
Definition init_state : state := l \\-> init_dstatelet.
Notation W := (mkWorld (TwoPhaseCoordinator.tpc l cn pts others Hnin)).
Program Definition run_coordinator : DHT [cn, _] ( fun i => network_rely W cn init_state i, fun _ m => exists (chs : seq bool), let: r := size data_stream in let: lg := seq.zip chs data_stream in getLocal cn (getStatelet m l) = st :-> (r, CInit) \+ log :-> lg /\ forall pt, pt \in pts -> getLocal pt (getStatelet m l) = st :-> (r, PInit) \+ log :-> lg) := Do (with_inv (TwoPhaseInductiveProof.ii _ _ _) coordinator).
Next Obligation.
move=>i/=R.
apply: with_inv_rule'.
apply:call_rule=>//.
-
by rewrite (rely_loc' _ R) /getStatelet findPt/=getCnLoc.
move=>_ m [chs] CS C I _.
exists chs.
split=>//.
move=>pt Hpt.
move /(coh_coh l) in C.
change l with (plab (TwoPhaseInductiveProof.tpc (cn :=cn) (pts := pts) l others Hnin)) in C.
rewrite prEq in C.
exact: (TwoPhaseInductiveInv.cn_log_agreement(l:=l)(others:=others)(Hnin:=Hnin) C CS I Hpt).
Program Definition run_participant p (pf : p \in pts) choices : DHT [p, _] ( fun i => network_rely W p init_state i, fun _ m => exists (lg : Log) (r : nat), getLocal p (getStatelet m l) = st :-> (r, PInit) \+ log :-> lg /\ forall pt' (ps' : PState) lg', pt' \in pts -> getLocal pt' (getStatelet m l) = st :-> (r, ps') \+ log :-> lg' -> lg = lg') := Do (with_inv (TwoPhaseInductiveProof.ii _ _ _ ) (participant p pf choices)).
Next Obligation.
move=>i/=R.
apply: with_inv_rule'.
apply:call_rule=>//.
-
by rewrite (rely_loc' _ R)/getStatelet findPt/= (getPLoc _ pf).
move=>_ m [bs][ds] PS C I _.
exists (seq.zip bs ds), (size choices).
move /(coh_coh l) in C.
change l with (plab (TwoPhaseInductiveProof.tpc (cn :=cn) (pts := pts) l others Hnin)) in C.
rewrite prEq in C.
split=>//.
move=>pt ps' lg' Hpt PS'.
apply/esym.
exact: (TwoPhaseInductiveInv.pt_log_agreement(l:=l)(others:=others)(Hnin:=Hnin) C pf PS I Hpt PS' erefl).
Program Definition run_participant1 := run_participant p1 _ choices1.
Program Definition run_participant2 := run_participant p2 _ choices2.
Program Definition run_participant3 := run_participant p3 _ choices3.
End SimpleTpcApp.
Definition data_seq := [:: [::1;2]; [::3;4]; [::5;6]; [::7;8]; [::9;10] ].
Definition choice_seq1 := [:: true; true; true; true; true].
Definition choice_seq2 := [:: true; false; true; true; true].
Definition choice_seq3 := [:: true; false; true; false; true].
Definition c_runner (u : unit) := run_coordinator data_seq.
Definition p_runner1 (u : unit) := run_participant1 choice_seq1.
Definition p_runner2 (u : unit) := run_participant1 choice_seq2.
Definition p_runner3 (u : unit) := run_participant1 choice_seq3.

Lemma hook_complete_unit (c : context) : hook_complete (c, Unit).
Proof.
by move=>????; rewrite dom0.

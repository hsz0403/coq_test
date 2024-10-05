From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype ssrfun seq.
From mathcomp Require Import path.
Require Import Eqdep.
Require Import Relation_Operators.
From fcsl Require Import pred prelude ordtype finmap pcm unionmap heap.
From DiSeL Require Import Freshness State EqTypeX Protocols Worlds NetworkSem Rely.
From DiSeL Require Import Actions Injection Process Always HoareTriples InferenceRules.
From DiSeL Require Import InductiveInv While.
From DiSeL Require Import CalculatorProtocol CalculatorInvariant.
From DiSeL Require Import CalculatorClientLib CalculatorServerLib.
From DiSeL Require Import DelegatingCalculatorServer SimpleCalculatorServers.
Export CalculatorProtocol.
Section CalculatorApp.
Definition l1 := 1.
Definition l2 := 2.
Definition f args := match args with | x::y::_ => Some (x + y) | _ => None end.
Definition prec (args : input) := if args is x::y::_ then true else false.
Definition cs1 := [::1].
Definition cls1 := [::2].
Definition cs2 := [::3].
Definition cls2 := [::1].
Notation nodes1 := (cs1 ++ cls1).
Notation nodes2 := (cs2 ++ cls2).
Notation cal1 := (cal_with_inv l1 f prec cs1 cls1).
Notation cal2 := (cal_with_inv l2 f prec cs2 cls2).
Notation W1 := (mkWorld cal1).
Notation W2 := (mkWorld cal2).
Definition V := W1 \+ W2.
Definition sv : nid := 1.
Definition cl : nid := 2.
Definition sd := 3.
Notation loc i k := (getLocal sv (getStatelet i k)).
Notation loc1 i := (loc i l1).
Notation loc2 i := (loc i l2).
Definition init_loc := st :-> ([::] : reqs).
Definition init_dstate1 := sv \\-> init_loc \+ cl \\-> init_loc.
Definition init_dstate2 := sv \\-> init_loc \+ sd \\-> init_loc.
Notation init_dstatelet1 := (DStatelet init_dstate1 Unit).
Notation init_dstatelet2 := (DStatelet init_dstate2 Unit).
Definition init_state : state := l1 \\-> init_dstatelet1 \+ l2 \\-> init_dstatelet2.
Definition client_input := [:: [::1; 2]; [::3; 4]; [::5; 6]; [::7; 8]; [::9; 10]].
Definition compute_input := compute_list_f l1 f prec cs1 cls1 cl Hc1 sv.
Program Definition client_run (u : unit) : DHT [cl, V] (fun i => network_rely V cl init_state i, fun (res : seq (input * nat)) m => [/\ all (fun e => f e.1 == Some e.2) res & client_input = map fst res]) := Do (uinject (compute_input client_input)).
Next Obligation.
rewrite -(unitR V)/V.
have V: valid (W1 \+ W2 \+ Unit) by rewrite unitR validV.
apply: (injectL V); do?[apply: hook_complete_unit | apply: hooks_consistent_unit].
by move=>??????; rewrite dom0.
Next Obligation.
move=>i/=R.
have X: injects W1 V Unit.
-
move: (@injectL W1 W2 Unit)=>/=; rewrite !unitR validV=>H.
apply: H=>//; do? [by apply: hook_complete0].
by move=>l _=>????; rewrite dom0.
case: (rely_ext X coh1 R)=>i1[j1][Z]C'; subst i.
apply: inject_rule=>//.
apply: call_rule=>C1{C'}/=; last by move=>m[H1]H2 H3.
have E: (getStatelet i1 l1) = (getStatelet (i1 \+ j1) l1).
-
by rewrite (locProjL (proj2 (rely_coh R)) _ C1)=>//; rewrite /W1 domPt.
rewrite E (rely_loc' _ R)/getLocal/=/getStatelet/=.
rewrite findUnL ?validI// domPt inE eqxx findPt/=.
by rewrite /init_dstate1 findUnR?valid_init_dstate1// domPt/= findPt/=.
Definition delegating_server (u : unit) := delegating_server_loop l1 l2 lab_dis f prec cs1 cls1 cs2 cls2 sv Hs1 Hc2 sd Hs2.
Program Definition server1_run (u : unit) : DHT [sv, V] (fun i => network_rely V sv init_state i, fun (res : unit) m => False) := Do (delegating_server u).
Next Obligation.
move=>i/=R; apply: call_rule=>C1//=.
rewrite (rely_loc' _ R)/getLocal/=/getStatelet/=.
rewrite findUnL ?validI ?valid_init_dstate1//.
rewrite domPt inE eqxx findPt/=.
rewrite findUnR ?validI ?valid_init_dstate1//=.
rewrite domPt inE/= findPt/=; split=>//.
rewrite -(rely_loc _ R)/=/getStatelet findUnR ?validI ?valid_init_dstate1//=.
rewrite domPt inE/= findPt/= /init_dstate2/=.
rewrite findUnL ?validI ?valid_init_dstate2//.
by rewrite domPt inE/= findPt/= /init_dstate2/=.
Definition secondary_server (u : unit) := with_inv (ii l2 f prec cs2 cls2) (memoizing_server l2 f prec prec_valid cs2 cls2 sd Hs2).
Program Definition server2_run (u : unit) : DHT [sd, V] (fun i => network_rely V sd init_state i, fun (res : unit) m => False) := Do _ (@inject sd W2 V Unit _ _ (secondary_server u);; ret _ _ tt).
Next Obligation.
rewrite -(unitR V)/V.
have V: valid (W1 \+ W2 \+ Unit) by rewrite unitR validV.
apply: (injectR V); do?[apply: hook_complete_unit | apply: hooks_consistent_unit].
by move=>??????; rewrite dom0.
Next Obligation.
move=>i/=R; apply: step.
rewrite /init_state joinC.
have X: injects W2 V Unit.
-
move: (@injectL W2 W1 Unit)=>/=; rewrite !unitR=>H.
rewrite /V joinC;apply: H=>//; do? [by apply: hook_complete0].
+
by rewrite joinC validV.
by move=>l _=>????; rewrite dom0.
rewrite /V joinC in R X; rewrite /init_state [l1 \\->_ \+ _]joinC in R.
case: (rely_ext X coh2 R)=>j1[i1][Z]C'; subst i.
apply: inject_rule=>//=.
apply: with_inv_rule; apply:call_rule=>//_.
have E: (getStatelet j1 l2) = (getStatelet (j1 \+ i1) l2).
-
by rewrite (locProjL (proj2 (rely_coh R)) _ C')=>//; rewrite /W1 domPt.
rewrite E (rely_loc' _ R)/getLocal/=/getStatelet/=.
rewrite findUnL ?validI//; last by rewrite joinC validI.
rewrite domPt/= findPt/=.
by rewrite /init_dstate2 findUnL ?valid_init_dstate2 ?domPt/= ?findPt.
End CalculatorApp.
Definition c_runner (u : unit) := client_run u.
Definition s_runner1 (u : unit) := server1_run u.
Definition s_runner2 (u : unit) := server2_run u.

Definition secondary_server (u : unit) := with_inv (ii l2 f prec cs2 cls2) (memoizing_server l2 f prec prec_valid cs2 cls2 sd Hs2).
Program Definition server2_run (u : unit) : DHT [sd, V] (fun i => network_rely V sd init_state i, fun (res : unit) m => False) := Do _ (@inject sd W2 V Unit _ _ (secondary_server u);; ret _ _ tt).
Next Obligation.
rewrite -(unitR V)/V.
have V: valid (W1 \+ W2 \+ Unit) by rewrite unitR validV.
apply: (injectR V); do?[apply: hook_complete_unit | apply: hooks_consistent_unit].
by move=>??????; rewrite dom0.

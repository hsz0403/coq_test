Require Import List Relation_Operators Operators_Properties Lia.
Import ListNotations.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab.
Require Import Undecidability.CounterMachines.CM2.
Require Import Undecidability.StringRewriting.Util.List_facts.
Require Import Undecidability.StringRewriting.Reductions.CM2_HALT_to_SSTS01.SR2ab_facts.
Require Import Undecidability.CounterMachines.Util.CM2_facts.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Local Arguments rt_trans {A R x y z}.
Local Arguments in_combine_l {A B l l' x y}.
Module Facts.
End Facts.
Module Argument.
Import Facts.
Local Arguments List.app : simpl never.
Local Arguments Nat.sub : simpl never.
Local Arguments repeat : simpl never.
Local Arguments app_inj_tail {A x y a b}.
Section Reduction.
Context (cm : Cm2).
Local Notation sb := ((0, @None nat)).
Local Notation sl := ((1, @None nat)).
Local Notation sr := ((2, @None nat)).
Local Notation sm := ((3, @None nat)).
Local Notation sz := ((4, @None nat)).
Local Notation so := ((5, @Some nat 0)).
Local Notation st := ((6, @None nat)).
Local Notation sb' p := ((0, @Some nat p)).
Local Notation sl' p := ((1, @Some nat p)).
Local Notation sr' p := ((2, @Some nat p)).
Local Notation sm' p := ((3, @Some nat p)).
Definition states := map (fun i => if i is dec _ q then q else 0) cm.
Definition sum : list nat -> nat := fold_right Nat.add 0.
Definition state_bound := 1 + length cm + sum states.
Definition enc_Instruction (ni: (nat * Instruction)) : Srs := match ni with | (p, inc b) => if b then [((sr' p, sz), (sb, sr' (S p)))] else [((sz, sl' p), (sl' (S p), sb))] | (p, dec b q) => if b then [((sm, sr' p), (sm, sr' (S p))); ((sb, sr' p), (sr' q, sz))] else [((sl' p, sm), (sl' (S p), sm)); ((sl' p, sb), (sz, sl' q))] end.
Definition srs : Srs := (* initialization *) [((sz, sz), (st, sr)); (* 00 -> tr *) ((sz, st), (sl' 0, sm)) (* 0t -> l_0 m *)] ++ (* simulation *) flat_map enc_Instruction (combine (seq 0 (length cm)) cm) ++ (* state movement to the right *) flat_map (fun p => [ ((sl' p, sb), (sl, sb' p)); ((sl' p, sm), (sl, sm' p)); ((sb' p, sb), (sb, sb' p)); ((sb' p, sm), (sb, sm' p)); ((sb' p, sr), (sb, sr' p)); ((sm' p, sb), (sm, sb' p)); ((sm' p, sr), (sm, sr' p))]) (seq 0 state_bound) ++ (* state movement to the left *) flat_map (fun p => [ ((sb, sr' p), (sb' p, sr)); ((sm, sr' p), (sm' p, sr)); ((sb, sb' p), (sb' p, sb)); ((sm, sb' p), (sm' p, sb)); ((sl, sb' p), (sl' p, sb)); ((sb, sm' p), (sb' p, sm)); ((sl, sm' p), (sl' p, sm))]) (seq 0 state_bound) ++ (* finalization *) map (fun p => ((sz, sl' p), (so, so))) (seq (length cm) (state_bound - length cm)) ++ [((sz, so), (so, so)); ((so, sb), (so, so)); ((so, sm), (so, so)); ((so, sr), (so, so)); ((so, sz), (so, so))].
Inductive srs_spec (a b c d: Symbol) : Prop := | srs_i0 : ((sz, sz), (st, sr)) = ((a, b), (c, d)) -> srs_spec a b c d | srs_i1 : ((sz, st), (sl' 0, sm)) = ((a, b), (c, d)) -> srs_spec a b c d | srs_sim0 {p} : ((sr' p, sz), (sb, sr' (S p))) = ((a, b), (c, d)) -> nth_error cm p = Some (inc true) -> srs_spec a b c d | srs_sim1 {p} : ((sz, sl' p), (sl' (S p), sb)) = ((a, b), (c, d)) -> nth_error cm p = Some (inc false) -> srs_spec a b c d | srs_sim2 {p q} : ((sm, sr' p), (sm, sr' (S p))) = ((a, b), (c, d)) -> nth_error cm p = Some (dec true q) -> srs_spec a b c d | srs_sim3 {p q} : ((sb, sr' p), (sr' q, sz))= ((a, b), (c, d)) -> nth_error cm p = Some (dec true q) -> srs_spec a b c d | srs_sim4 {p q} : ((sl' p, sm), (sl' (S p), sm)) = ((a, b), (c, d)) -> nth_error cm p = Some (dec false q) -> srs_spec a b c d | srs_sim5 {p q} : ((sl' p, sb), (sz, sl' q)) = ((a, b), (c, d)) -> nth_error cm p = Some (dec false q) -> srs_spec a b c d | srs_fin0 {p} : ((sz, sl' p), (so, so)) = ((a, b), (c, d)) -> length cm <= p < state_bound -> srs_spec a b c d | srs_fin1 : ((sz, so), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d | srs_fin2 : ((so, sb), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d | srs_fin3 : ((so, sm), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d | srs_fin4 : ((so, sr), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d | srs_fin5 : ((so, sz), (so, so)) = ((a, b), (c, d)) -> srs_spec a b c d.
Inductive srs_mlr_spec (a b c d: Symbol) : Prop := | srs_mr0 {p} : ((sl' p, sb), (sl, sb' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_mr1 {p} : ((sl' p, sm), (sl, sm' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_mr2 {p} : ((sb' p, sb), (sb, sb' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_mr3 {p} : ((sb' p, sm), (sb, sm' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_mr4 {p} : ((sb' p, sr), (sb, sr' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_mr5 {p} : ((sm' p, sb), (sm, sb' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_mr6 {p} : ((sm' p, sr), (sm, sr' p)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_ml0 {p} : ((sb, sr' p), (sb' p, sr)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_ml1 {p} : ((sm, sr' p), (sm' p, sr)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_ml2 {p} : ((sb, sb' p), (sb' p, sb)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_ml3 {p} : ((sm, sb' p), (sm' p, sb)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_ml4 {p} : ((sl, sb' p), (sl' p, sb)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_ml5 {p} : ((sb, sm' p), (sb' p, sm)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d | srs_ml6 {p} : ((sl, sm' p), (sl' p, sm)) = ((a, b), (c, d)) -> p < state_bound -> srs_mlr_spec a b c d.
Local Create HintDb in_srs_db.
Local Hint Resolve or_introl or_intror conj In_srsI : in_srs_db.
Local Hint Immediate erefl : in_srs_db.
Local Hint Constructors srs_spec srs_mlr_spec : in_srs_db.
Definition stepI_nil := (@step_intro srs []).
Section Transport.
Context (n_cm: nat).
Definition c0 := {| state := 0; value1 := 0; value2 := 0 |}.
Context (H_n_cm: halting cm (Nat.iter n_cm (CM2.step cm) c0)).
Definition d := 5 + n_cm + n_cm.
Definition enc_Config : Config -> list Symbol := fun '{| state := p; value1 := a; value2 := b |} => (repeat sz (1 + n_cm-a)) ++ [sl' p] ++ (repeat sb a) ++ [sm] ++ (repeat sb b) ++ [sr] ++ (repeat sz (1 + n_cm-b)).
Definition enc_Config' : Config -> list Symbol := fun '{| state := p; value1 := a; value2 := b |} => (repeat sz (1 + n_cm-a)) ++ [sl] ++ (repeat sb a) ++ [sm] ++ (repeat sb b) ++ [sr' p] ++ (repeat sz (1 + n_cm-b)).
End Transport.
Section InverseTransport.
Context (N: nat).
Context (HN: multi_step srs (repeat sz (1+N)) (repeat so (1+N))).
Local Definition rt_rt1n {A R x y} := @clos_rt_rt1n_iff A R x y.
Definition encodes : Config -> list Symbol -> Prop := fun c s => exists u v t, let '{| state := p; value1 := a; value2 := b |} := c in s = u ++ t ++ v /\ map fst t = map fst ([sl] ++ repeat sb a ++ [sm] ++ repeat sb b ++ [sr]) /\ filter (fun x => if x is None then false else true) (map snd t) = [Some p].
Inductive srs_step_spec (u v: list Symbol) (a b: Symbol) (n m: nat) : Prop := | srs_step0 : a.1 = sl.1 -> b.1 = sm.1 -> u = [] -> n = 0 -> srs_step_spec u v a b n m | srs_step1 : a.1 = sl.1 -> b.1 = sb.1 -> u = [] -> n = 1 + (n - 1) -> srs_step_spec u v a b n m | srs_step2 : a.1 = sm.1 -> b.1 = sr.1 -> v = [] -> m = 0 -> srs_step_spec u v a b n m | srs_step3 : a.1 = sb.1 -> b.1 = sr.1 -> v = [] -> m = 1 + (m - 1) -> srs_step_spec u v a b n m.
End InverseTransport.
End Reduction.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma move_sb_right {p n} : p < state_bound -> multi_step srs ((sb' p) :: repeat sb n) ((repeat sb n) ++ [sb' p]).
Proof.
move=> Hp.
elim: n; first by apply: rt_refl.
move=> n IH /=.
apply: rt_trans; [apply: rt_step | apply: (multi_step_applI (u := [sb])); exact: IH].
apply: stepI_nil.
by eauto with in_srs_db nocore.

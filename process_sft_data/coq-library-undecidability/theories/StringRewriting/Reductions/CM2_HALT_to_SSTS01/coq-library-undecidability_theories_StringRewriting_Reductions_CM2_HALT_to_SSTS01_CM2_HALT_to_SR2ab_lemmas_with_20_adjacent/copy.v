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

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Proof.
Admitted.

Lemma nth_error_Some_in_combine {X: Type} {l: list X} {i x}: nth_error l i = Some x -> In (i, x) (combine (seq 0 (length l)) l).
Proof.
move Hk: (0) => k Hi.
have ->: (i = i + k) by lia.
elim: l i k {Hk} Hi; first by case.
move=> y l IH [|i] k.
-
move=> /= [<-].
by left.
-
move=> /IH {}IH /=.
right.
Admitted.

Lemma inv_nth_error_Some_in_combine {X: Type} {l: list X} {i x}: In (i, x) (combine (seq 0 (length l)) l) -> nth_error l i = Some x.
Proof.
move Hk: (0) => k.
rewrite [in (_, _)](ltac:(lia) : (i = i + k)).
elim: l i k {Hk}; first by case.
move=> y l IH i k /= [].
-
move=> [? ->].
by have ->: i = 0 by lia.
-
move: i => [|i].
+
move=> /in_combine_l /in_seq.
by lia.
+
have ->: S i + k = i + S k by lia.
Admitted.

Lemma state_boundP {p i} : nth_error cm p = Some i -> (if i is dec _ q then q else 0) + 1 + p < state_bound.
Proof.
rewrite /state_bound /states.
elim: (cm) p; first by case.
move=> ? l IH [|p] /= => [[->] | /IH]; last by lia.
Admitted.

Lemma srs_specI a b c d : In ((a, b), (c, d)) srs -> srs_spec a b c d \/ srs_mlr_spec a b c d.
Proof.
rewrite /srs.
case /in_app_iff.
{
firstorder (by eauto using srs_spec with nocore).
}
case /in_app_iff.
{
move=> /in_flat_map [[? i]] [/inv_nth_error_Some_in_combine].
move: i => [] [] > /=; firstorder (by eauto using srs_spec with nocore).
}
case /in_app_iff.
{
move=> /in_flat_map [?] [/in_seq] [_ ?].
firstorder (by eauto using srs_mlr_spec with nocore).
}
case /in_app_iff.
{
move=> /in_flat_map [?] [/in_seq] [_ ?].
firstorder (by eauto using srs_mlr_spec with nocore).
}
case /in_app_iff.
{
move=> /in_map_iff [?] [?] /in_seq H.
left.
apply: srs_fin0; first by eassumption.
move: H.
rewrite /state_bound.
by lia.
}
Admitted.

Lemma In_srsI {a b c d} : srs_spec a b c d \/ srs_mlr_spec a b c d -> In ((a, b), (c, d)) srs.
Proof.
case.
-
move=> [] > <- *.
1-2: apply /In_appl; rewrite /=; by tauto.
1-6: apply /In_appr /In_appl /in_flat_map; eexists; (constructor; [apply: nth_error_Some_in_combine; by eassumption | by move=> /=; tauto ]).
1: apply /In_appr /In_appr /In_appr /In_appr /In_appl /in_map_iff; eexists; (constructor; [by reflexivity | apply /in_seq; by lia ]).
1-5: do 5 (apply /In_appr); move=> /=; by tauto.
-
move=> [] p <- *.
1-7: apply /In_appr /In_appr /In_appl /in_flat_map; exists p; (constructor; [apply /in_seq; by lia | by move=> /=; tauto ]).
Admitted.

Lemma srs_mlr_specE {a b c d} : srs_mlr_spec a b c d -> exists x y p, ((a, b), (c, d)) = (((x, Some p), (y, None)), ((x, None), (y, Some p))) \/ ((a, b), (c, d)) = (((x, None), (y, Some p)), ((x, Some p), (y, None))).
Proof.
Admitted.

Lemma move_sb_right {p n} : p < state_bound -> multi_step srs ((sb' p) :: repeat sb n) ((repeat sb n) ++ [sb' p]).
Proof.
move=> Hp.
elim: n; first by apply: rt_refl.
move=> n IH /=.
apply: rt_trans; [apply: rt_step | apply: (multi_step_applI (u := [sb])); exact: IH].
apply: stepI_nil.
Admitted.

Lemma move_sb_left {p n} : p < state_bound -> multi_step srs ((repeat sb n) ++ [sb' p]) ((sb' p) :: repeat sb n).
Proof.
move=> Hp.
elim: n; first by apply: rt_refl.
move=> n IH /=.
apply: rt_trans; [apply: (multi_step_applI (u := [sb])); exact: IH | apply: rt_step].
apply: stepI_nil.
Admitted.

Lemma cm_values_ub n : value1 (Nat.iter n (CM2.step cm) c0) + value2 (Nat.iter n (CM2.step cm) c0) <= n_cm.
Proof using H_n_cm.
have [|->] : n <= n_cm \/ n = ((n - n_cm) + n_cm) by lia.
-
move=> ?.
have := values_ub cm c0 n.
rewrite /c0 /=.
by lia.
-
rewrite iter_plus halting_eq; first done.
have := values_ub cm c0 n_cm.
rewrite /c0 /=.
Admitted.

Lemma cm_state_ub n : state (Nat.iter n (CM2.step cm) c0) < state_bound.
Proof.
elim: n; first by (rewrite /= /state_bound; lia).
move=> n /=.
move: (Nat.iter _ _ c0) => [p a b] /=.
move Hoi: (nth_error cm p) => oi.
case: oi Hoi; last done.
case.
-
by move=> > /state_boundP.
-
Admitted.

Lemma multi_step_enc_c0 : multi_step srs (repeat sz d) (enc_Config c0).
Proof using.
apply: (rt_trans (y := (repeat sz (1 + n_cm)) ++ [sz] ++ [st] ++ [sr] ++ (repeat sz (1 + n_cm)))).
-
have ->: d = 1 + n_cm + 1 + 1 + 1 + 1 + n_cm by (rewrite /d; lia).
rewrite -?repeat_appP -?app_assoc.
do ? apply: multi_step_applI.
apply /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
-
apply /multi_step_applI /rt_step /stepI_nil.
Admitted.

Lemma move_sb_right' {p n x y} : p < state_bound -> ((x, y) = (1, 3) \/ (x, y) = (3, 2)) -> multi_step srs ([(x, Some p)] ++ repeat sb n ++ [(y, None)]) ([(x, None)] ++ repeat sb n ++ [(y, Some p)]).
Proof.
move=> ? /= Hxy.
case: n.
-
apply /rt_step /stepI_nil.
move: Hxy => [] [-> ->]; by eauto with in_srs_db nocore.
-
move=> n.
apply: (rt_trans (y := [(x, None)] ++ [sb' p] ++ (repeat sb n) ++ [(y, None)])).
+
have ->: repeat sb (S n) = [sb] ++ repeat sb n by done.
rewrite /= -?app_assoc.
apply /rt_step /stepI_nil.
move: Hxy => [] [-> _]; by eauto with in_srs_db nocore.
+
rewrite -?app_assoc.
apply: multi_step_applI.
apply: (rt_trans (y := (repeat sb n) ++ [sb' p] ++ [(y, None)])).
*
rewrite ?app_assoc.
apply: multi_step_apprI.
by apply: move_sb_right.
*
have ->: S n = n + 1 by lia.
rewrite -repeat_appP -?app_assoc.
apply /multi_step_applI /rt_step /stepI_nil.
Admitted.

Lemma move_sb_left' {p n x y} : p < state_bound -> ((x, y) = (1, 3) \/ (x, y) = (3, 2)) -> multi_step srs ([(x, None)] ++ repeat sb n ++ [(y, Some p)]) ([(x, Some p)] ++ repeat sb n ++ [(y, None)]).
Proof.
move=> ? /= Hxy.
case: n.
-
apply /rt_step /stepI_nil.
move: Hxy => [] [-> ->]; by eauto with in_srs_db nocore.
-
move=> n.
apply: (rt_trans (y := [(x, None)] ++ (repeat sb n) ++ [sb' p] ++ [(y, None)])).
+
rewrite (ltac:(lia) : S n = n + 1) -repeat_appP -?app_assoc.
do ? apply: multi_step_applI.
apply /rt_step /stepI_nil.
move: Hxy => [] [_ ->]; by eauto with in_srs_db nocore.
+
rewrite ?app_assoc.
apply: multi_step_apprI.
apply: (rt_trans (y := [(x, None)] ++ [sb' p] ++ (repeat sb n))).
*
rewrite -?app_assoc.
apply: multi_step_applI.
by apply: move_sb_left.
*
apply /rt_step /stepI_nil.
Admitted.

Lemma move_right n : let c := (Nat.iter n (CM2.step cm) c0) in multi_step srs (enc_Config c) (enc_Config' c).
Proof.
move=> c.
subst c.
have := cm_state_ub n.
move: (Nat.iter n _ c0) => [p a b] /= ?.
apply: multi_step_applI.
rewrite ?app_assoc.
apply: multi_step_apprI.
apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
-
rewrite ?app_assoc.
do 2 apply: multi_step_apprI.
apply: move_sb_right'; by tauto.
-
rewrite -?app_assoc.
do 2 apply: multi_step_applI.
Admitted.

Lemma move_left n : let c := (Nat.iter n (CM2.step cm) c0) in multi_step srs (enc_Config' c) (enc_Config c).
Proof.
move=> c.
subst c.
have := cm_state_ub n.
move: (Nat.iter n _ c0) => [p a b] /= ?.
apply: multi_step_applI.
rewrite ?app_assoc.
apply: multi_step_apprI.
apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
-
rewrite -?app_assoc.
do 2 apply: multi_step_applI.
apply: move_sb_left'; by tauto.
-
rewrite ?app_assoc.
do 2 apply: multi_step_apprI.
Admitted.

Lemma simulate_cm_step {n} : let c := (Nat.iter n (CM2.step cm) c0) in multi_step srs (enc_Config c) (enc_Config (CM2.step cm c)).
Proof using H_n_cm.
move=> c.
subst c.
have := cm_values_ub n.
have := move_right n.
have := move_left (1+n).
move=> /=.
case: (Nat.iter n _ _) => p a b /=.
move Hoi: (nth_error cm p) => oi.
case: oi Hoi; last by (move=> *; apply: rt_refl).
case; case.
-
move=> ? /= Hr Hl ?.
apply: rt_trans; first by eassumption.
apply: rt_trans; last by eassumption.
have [-> ->]: S b = b + 1 /\ S n_cm - b = 1 + (S n_cm - (b + 1)) by lia.
rewrite -?repeat_appP -?app_assoc.
do 5 apply: multi_step_applI.
apply /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
-
move=> ? _ _ ? /=.
have [-> ->]: S n_cm - a = (n_cm - a) + 1 /\ S a = 1 + a by lia.
rewrite -?repeat_appP -?app_assoc.
apply: multi_step_applI.
apply /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
-
move=> q ? /= Hr Hl Hb.
apply: rt_trans; first by eassumption.
apply: rt_trans; last by eassumption.
case: (b) Hb => [_ | b' Hb'] /=.
+
do 3 apply: multi_step_applI.
apply /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
+
have [-> ->] : S b' = b' + 1 /\ S n_cm - b' = 1 + (S n_cm - (b' + 1)) by lia.
rewrite -?repeat_appP -?app_assoc.
do 5 apply: multi_step_applI.
apply /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
-
move=> q ? _ _ Ha.
case: (a) Ha => [_ | a' Ha'] /=.
+
apply /multi_step_applI /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
+
rewrite (ltac:(lia) : (S n_cm - a' = (n_cm - a') + 1)) -repeat_appP -?app_assoc.
apply /multi_step_applI /rt_step /stepI_nil.
Admitted.

Lemma multi_step_repeat_solI n : multi_step srs (repeat sz n ++ [so]) (repeat so (n+1)).
Proof.
elim: n; first by apply: rt_refl.
move=> n IH.
rewrite -repeat_appP.
have ->: S n = n + 1 by lia.
apply: (rt_trans (y := repeat sz n ++ [so] ++ [so])); last by (rewrite ?app_assoc; apply: multi_step_apprI).
rewrite -repeat_appP -?app_assoc.
apply /multi_step_applI /rt_step /stepI_nil.
Admitted.

Lemma multi_step_repeat_sorI {n x} : x = sb \/ x = sz -> multi_step srs ([so] ++ repeat x n) ([so] ++ repeat so n).
Proof.
move=> Hx.
elim: n; first by apply: rt_refl.
move=> n IH.
apply: (rt_trans (y := ([so] ++ [so] ++ repeat x n))); last by apply: multi_step_applI.
apply /rt_step /stepI_nil.
Admitted.

Lemma multi_step_repeat_sorI' {s t n x} : x = sb \/ x = sz -> multi_step srs ([so] ++ s) ([so] ++ t) -> multi_step srs ([so] ++ repeat x n ++ s) ([so] ++ repeat so n ++ t).
Proof.
move=> /multi_step_repeat_sorI H1 H2.
apply: (rt_trans (y := ([so] ++ repeat so n ++ s))).
-
rewrite ?app_assoc.
by apply: multi_step_apprI.
-
have ->: [so] = repeat so 1 by done.
rewrite ?app_assoc repeat_appP.
have ->: 1 + n = n + 1 by lia.
rewrite -repeat_appP -?app_assoc.
Admitted.

Lemma copy {A : Prop} : A -> A * A.
Proof.
done.

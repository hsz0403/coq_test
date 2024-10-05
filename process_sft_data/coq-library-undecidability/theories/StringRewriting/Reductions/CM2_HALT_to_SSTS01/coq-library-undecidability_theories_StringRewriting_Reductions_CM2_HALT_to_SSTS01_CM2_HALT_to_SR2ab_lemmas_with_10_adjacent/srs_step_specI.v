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

Lemma simulate_cm_halting {n} : let c := (Nat.iter n (CM2.step cm) c0) in halting cm c -> multi_step srs (enc_Config c) (repeat so d).
Proof using H_n_cm.
move=> c /haltingP.
subst c.
have := cm_values_ub n.
have := cm_state_ub n.
move: (Nat.iter _ _ c0) => [p a b] /= *.
apply: (rt_trans (y := (repeat sz (n_cm - a)) ++ [so] ++ [so] ++ _)).
-
rewrite (ltac:(lia) : S n_cm - a = (n_cm - a) + 1) -repeat_appP -?app_assoc.
apply /multi_step_applI /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
-
apply: (rt_trans (y := (repeat so (n_cm - a + 1) ++ [so] ++ repeat sb a ++ [sm] ++ repeat sb b ++ [sr] ++ repeat sz (S n_cm - b)))).
+
rewrite ?app_assoc.
do 6 apply: multi_step_apprI.
by apply: multi_step_repeat_solI.
+
have ->: d = (n_cm - a + 1) + 1 + a + 1 + b + 1 + (S n_cm - b) by (rewrite /d; lia).
rewrite -?repeat_appP -?app_assoc.
do 2 apply: multi_step_applI.
apply: multi_step_repeat_sorI'; first by left.
apply: (rt_trans (y := ([so] ++ [so] ++ repeat sb b ++ [sr] ++ repeat sz (S n_cm - b)))).
*
apply /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
*
apply: multi_step_applI.
apply: multi_step_repeat_sorI'; first by left.
apply: (rt_trans (y := ([so] ++ [so] ++ repeat sz (S n_cm - b)))).
**
apply /rt_step /stepI_nil.
by eauto with in_srs_db nocore.
**
apply: multi_step_applI.
apply: multi_step_repeat_sorI.
Admitted.

Lemma transport : CM2_HALT cm -> SR2ab (srs, sz, so).
Proof.
move=> [n /copy [Hn] /(simulate_cm_halting n Hn) H].
exists (@d n - 1).
apply: rt_trans; last by eassumption.
apply: rt_trans; first by apply: (multi_step_enc_c0).
elim: (n in Nat.iter n); first by apply: rt_refl.
move=> m IH {H}.
Admitted.

Lemma In_srs_stE {a b c d} : In ((a, b), (c, d)) srs -> ((sz, sz), (st, sr)) = ((a, b), (c, d)) \/ ((sz, st), (sl' 0, sm)) = ((a, b), (c, d)) \/ if a is (_, None) then (if b is (_, None) then False else True) else True.
Proof.
Admitted.

Lemma init_encodes : exists s, encodes c0 s /\ multi_step srs s (repeat so (1+N)).
Proof using HN.
have [s] : exists s, multi_step srs s (repeat so (1+N)) /\ Forall (fun x => snd x = None) s /\ forall n, nth n s sz = st -> nth (1+n) s sz = sr.
{
eexists.
constructor; [|constructor]; [by eassumption | apply /Forall_repeatI; by tauto |].
move: (1+N) => m n H.
exfalso.
elim: n m H; first by case.
move=> n IH [|m]; [done | by apply: IH].
}
move Ht: (repeat so (1+N)) => t [/rt_rt1n Hst] [].
elim: Hst Ht; first by move=> ? <- /ForallE [].
move=> {}s {}t > Hst Ht IH /IH {IH}.
case: Hst Ht => u v a b c d /In_srs_stE [|[]].
-
move=> [] <- <- <- <- _ IH.
move=> /Forall_app [Hu] /ForallE [_] /ForallE [_ Ht] Huv.
apply: IH.
+
apply /Forall_app.
by do ? constructor.
+
move=> n.
have := Huv n.
elim: (u) n; first by move=> [|[|n]].
clear.
move=> x {}u IH [|n]; last by move/IH.
move: (u) => [|? ?]; [by move=> H /H | done].
-
move=> [] <- <- <- <- /rt_rt1n Ht _ _ /(_ (1 + length u)).
do 2 (rewrite app_nth2; first by lia).
rewrite (ltac:(lia) : 1 + length u - length u = 1).
rewrite (ltac:(lia) : 1 + (1 + length u) - length u = 2).
move=> /(_ ltac:(done)) Hv.
eexists.
constructor; last by eassumption.
move: (v) Hv => [|? v']; first done.
move=> /= ->.
exists u, v', [sl' 0; sm; sr].
constructor; [done | by constructor].
-
move=> H _ _ /Forall_app [_] /ForallE [+] /ForallE [+] _.
Admitted.

Lemma eq2_app {u v a b} {s t: list Symbol} : u ++ a :: b :: v = s ++ t -> (exists v1, v = v1 ++ t /\ s = u ++ a :: b :: v1) \/ (s = u ++ [a] /\ t = b :: v) \/ (exists u2, u = s ++ u2 /\ t = u2 ++ a :: b :: v).
Proof.
elim: u s.
-
move=> [|y1 [|y2 s]].
+
rewrite ?app_nil_l.
move=> <-.
right.
right.
by exists [].
+
move=> [] <- <- /=.
right.
by left.
+
move=> [] <- <- ->.
left.
by exists s.
-
move=> x1 u IH [|y1 s].
+
rewrite ?app_nil_l.
move=> <-.
right.
right.
by exists (x1 :: u).
+
move=> [] <- /IH [|[|]].
*
move=> [?] [-> ->].
left.
by eexists.
*
move=> [-> ->].
right.
by left.
*
move=> [?] [-> ->].
right.
right.
Admitted.

Lemma eq2_app_app {u a b v u' v'} {s: list Symbol} : length s > 1 -> u ++ a :: b :: v = u' ++ s ++ v' -> (exists u'2, v = u'2 ++ s ++ v') \/ (exists s2, u' = u ++ [a] /\ s = b :: s2 /\ v = s2 ++ v') \/ (exists s1 s2, s = s1 ++ [a] ++ [b] ++ s2 /\ u = u' ++ s1 /\ v = s2 ++ v') \/ (exists s1, u = u' ++ s1 /\ s = s1 ++ [a] /\ v' = b :: v) \/ (exists v'1, u = u' ++ s ++ v'1).
Proof.
move=> Hs /eq2_app [|[|]].
-
move=> [?] [-> ->].
left.
by eexists.
-
move=> [->].
move: s Hs => [|? s] /=; first by lia.
move=> _ [] <- <-.
right.
left.
by eexists.
-
move=> [?] [->] /esym /eq2_app [|[|]].
+
move=> [?] [-> ->].
right.
right.
left.
by do 2 eexists.
+
move=> [-> ->].
do 3 right.
left.
by eexists.
+
move=> [?] [-> ->].
do 4 right.
Admitted.

Lemma simulate_srs_step {c s t} : SR2ab.step srs s t -> encodes c s -> halting cm c \/ encodes c t \/ encodes (CM2.step cm c) t.
Proof.
move: c => [p a b] [] u v a' b' c' d' H [u'] [v'] [{}t].
rewrite -?/([_] ++ [_] ++ v).
move=> [+] [H1t H2t] => /eq2_app_app.
have : length t > 1.
{
move: H1t => /(congr1 (@length _)).
rewrite ?map_app ?app_length ?map_length /=.
move=> ->.
by lia.
}
move=> Ht /(_ Ht) {Ht}.
case; [|case; [|case; [|case]]].
-
move=> [u'2 ->].
right.
left.
exists (u ++ c' :: d' :: u'2), v', t.
constructor; [by rewrite -?app_assoc | done].
-
move=> [s2] [?] [? ?].
subst.
move: H1t H2t => [].
move: H => /srs_specI [|] [] > [] ? ? ? ?; subst; try done; [|].
+
move=> Hi _ H1s2 [<- H2s2].
right.
right.
rewrite /= Hi.
eexists u, v', (_ :: _ :: s2).
constructor; [done | constructor; by rewrite /= ?H1s2 ?H2s2].
+
move=> ? _ _ [<-] _ *.
left.
apply /haltingP => /=.
by lia.
-
move=> [s1] [s2] [?] [? ?].
subst.
move: H H1t H2t => /srs_specI [].
+
move=> H + + /ltac:(right; right).
move=> /copy [/srs_step_specI] [].
*
move=> H'.
move: H' H => [] ? ? ? ? [] > [] ? ? ? ?; subst; try done; [ | | | ].
**
rewrite app_nil_r /=.
move=> + [H1] [<-] => -> H2.
eexists u', v', (_ :: _ :: _).
constructor; [done | by rewrite /= H1 H2].
**
rewrite app_nil_r /= ?map_app.
move: (a) => [|?]; first done.
move=> + [] H1 [<-] H2 => ->.
eexists (u' ++ [sz]), v', (_ :: _).
rewrite -?app_assoc.
constructor; [done | by rewrite /= ?map_app H1 H2].
**
rewrite ?map_app filter_app /= app_nil_r.
move=> + + /(app_inj_tail (y := [])) [H2] [<-].
move=> ->.
rewrite ?app_assoc app_nil_r.
move=> /app_inj_tail [/app_inj_tail] [H1] _ _.
eexists u', v', (_ ++ [_; _]).
rewrite -?app_assoc.
constructor; first done.
by rewrite ?map_app filter_app /= H1 H2.
**
rewrite [in repeat sb b](ltac:(lia) : b = (b - 1) + 1) -repeat_appP.
rewrite ?map_app ?filter_app ?app_assoc ?app_nil_r /=.
move=> + + /(app_inj_tail (y := [])) [H2] [<-].
move=> ->.
move=> /app_inj_tail [/app_inj_tail] [H1] _ _.
eexists u', ([sz] ++ v'), (_ ++ [_]).
rewrite (ltac:(lia) : b = 1 + (b - 1)) -?app_assoc /=.
constructor; first done.
by rewrite ?map_app filter_app /= H1 H2 -?app_assoc.
*
move: H => + + _ /ltac:(exfalso).
move=> [] > [] *; subst; by firstorder done.
+
move=> + + + /ltac:(right; left; exists u', v', (s1 ++ c' :: d' :: s2)).
move=> /srs_mlr_specE [x] [y] [q] [] [] ? ? ? ? H1t H2t; subst; rewrite -?app_assoc.
*
constructor; first done.
constructor; first by rewrite -H1t ?map_app.
move: H2t.
by rewrite ?map_app ?filter_app /=.
*
constructor; first done.
constructor; first by rewrite -H1t ?map_app.
move: H2t.
by rewrite ?map_app ?filter_app /=.
-
move=> [s1] [?] [? ?].
subst.
move: (H1t).
rewrite ?map_app ?app_assoc.
move=> /app_inj_tail [_].
move: H H1t H2t => /srs_specI [|] [] > [] ? ? ? ?; subst; try done; [].
move=> Hi H1s1.
rewrite map_app filter_app.
move=> /(app_inj_tail (y := [])) [H2s2] [<-] _.
right.
right.
rewrite /= Hi.
eexists u', v, (s1 ++ [_; _]).
rewrite -?app_assoc.
constructor; [done | constructor].
*
move: H1s1.
rewrite ?map_app ?app_assoc.
move=> /app_inj_tail [-> _].
by rewrite (ltac:(lia) : 1 + b = b + 1) -[repeat _ (b + 1)]repeat_appP map_app -?app_assoc.
*
by rewrite map_app filter_app /= H2s2.
-
move=> [v'1 ->].
right.
left.
exists u', (v'1 ++ c' :: d' :: v), t.
Admitted.

Lemma halting_cmI : exists n, halting cm (Nat.iter n (CM2.step cm) c0).
Proof using HN.
have [s [H1s H2s]] := init_encodes.
move Ht: (repeat so (1+N)) (c0) H2s H1s => t c Hst.
have {}Ht : Forall (fun x => fst so = x) (map fst t).
{
subst t.
elim: (N); by constructor.
}
move: Hst Ht c.
move=> /rt_rt1n.
elim.
-
move=> {}s Hs [? ? ?] /= [?] [?] [{}t] [?] [H].
subst s.
move: Hs.
rewrite ?map_app ?Forall_app H.
by move=> [_] [/ForallE] [].
-
move=> > /simulate_srs_step H _ IH /IH {}IH c /H {H} [|[]].
+
move=> ?.
by exists 0.
+
by move=> /IH.
+
move=> /IH [n Hn].
exists (n + 1).
Admitted.

Lemma inverse_transport : SR2ab (srs, sz, so) -> CM2_HALT cm.
Proof.
move=> [n Hn].
apply: halting_cmI.
Admitted.

Theorem reduction : CM2_HALT ⪯ SR2ab.
Proof.
exists (fun cm => (Argument.srs cm, (4, None), (5, Some 0))).
intro cm.
constructor.
-
exact (Argument.transport cm).
-
Admitted.

Lemma srs_step_specI {u v a b n m} : map fst (u ++ [a] ++ [b] ++ v) = map fst ([sl] ++ repeat sb n ++ [sm] ++ repeat sb m ++ [sr]) -> srs_step_spec u v a b n m \/ (a.1 = sb.1 /\ b.1 = sb.1) \/ (a.1 = sb.1 /\ b.1 = sm.1) \/ (a.1 = sm.1 /\ b.1 = sb.1).
Proof.
move: u => [|? u].
{
move: n => [|n].
-
move=> [] *.
left.
by apply: srs_step0.
-
move=> [] *.
left.
apply: srs_step1; by [|lia].
}
move=> [] _.
rewrite -/(_ ++ _).
elim /rev_ind: v.
{
rewrite app_nil_r ?map_app /=.
rewrite ?app_assoc.
move=> /app_inj_tail [].
have [->|->] : m = 0 \/ m = (m - 1) + 1 by lia.
-
rewrite app_nil_r.
move=> /app_inj_tail [] *.
left.
by apply: srs_step2.
-
rewrite -repeat_appP map_app ?app_assoc.
move=> /app_inj_tail [] *.
left.
apply: srs_step3; by [|lia].
}
move=> ? v _.
rewrite ?map_app ?app_assoc.
move=> /app_inj_tail [+] _.
move=> + /ltac:(right).
elim: u n.
{
move=> [|[|n]].
-
move: m => [|m [] *]; [done | by tauto ].
-
move=> [] *.
by tauto.
-
move=> [] *.
by tauto.
}
move=> ? u IH [|n]; last by move=> [_] /IH.
move=> [_] {IH}.
rewrite -?/(_ ++ _).
elim: m u; first by case.
move=> m IH [|? u]; last by move=> [_] /IH.
move: m {IH} => [|m] []; [done | by tauto].

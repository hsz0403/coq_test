Require Export Undecidability.TM.Code.CodeTM Undecidability.TM.Code.Copy Undecidability.TM.Code.ChangeAlphabet Undecidability.TM.Code.WriteValue.
Require Export Undecidability.TM.Compound.TMTac.
Require Export Undecidability.TM.Basic.Mono Undecidability.TM.Compound.Multi.
Require Import Lia.
Export Set Default Proof Using "Type".
Ltac clear_tape_eqs := repeat once lazymatch goal with | [ H: ?t'[@ ?x] = ?t[@ ?x] |- _ ] => clear H end.
Tactic Notation "destruct" "_" "in" constr(H):= match type of H with | context[match ?X with _ => _ end] => destruct X | context[match ?X with _ => _ end] => destruct X end.
Tactic Notation "tacInEvar" constr(E) tactic3(tac) := is_evar E; let t := type of E in let __tmp_callInEvar := fresh "__tmp_callInEvar" in evar (__tmp_callInEvar:t); (only [__tmp_callInEvar]:tac);unify E __tmp_callInEvar;subst __tmp_callInEvar;instantiate.
Tactic Notation "introsSwitch" ne_simple_intropattern_list(P):= once lazymatch goal with |- (forall f' , ?REL _ (?Rmove f')) => tacInEvar Rmove intros P;cbn beta;intros P end.
Tactic Notation "destructBoth" constr(g) "as" simple_intropattern(P) := once lazymatch goal with |- (RealiseIn _ ?Rmove _) => tacInEvar Rmove (destruct g as P);destruct g as P;cbn zeta iota beta | |- (?REL _ ?Rmove) => tacInEvar Rmove (destruct g as P);destruct g as P;cbn zeta iota beta end.
Tactic Notation "destructBoth" constr(g) := destructBoth g as [].
Tactic Notation "infTer" int_or_var(n) := let t := try (first [match goal with |- exists x:_,_ => simple notypeclasses refine (@ex_intro _ _ _ _);[shelve|cbn beta] end | simple apply conj | simple eapply Nat.le_refl]) in t;do n t.
Tactic Notation "length_not_eq" "in" constr(H):= let H' := fresh "H" in specialize (f_equal (@length _) H) as H';repeat (try autorewrite with list in H';cbn in H');nia.
Ltac length_not_eq := let H := fresh "H" in intros H;exfalso;length_not_eq in H.
Ltac specializeFin H' := match type of H' with forall i : Fin.t ?n, _ => do_n_times_fin n ltac:(fun i => let H := fresh H' in specialize (H' i) as H;cbn in H) end.
From Coq.ssr Require ssrfun.
Module Option := ssrfun.Option.
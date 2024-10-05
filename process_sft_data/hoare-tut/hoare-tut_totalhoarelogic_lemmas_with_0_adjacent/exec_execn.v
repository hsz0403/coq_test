Global Set Asymmetric Patterns.
Set Implicit Arguments.
Require Export hoarelogicsemantics.
Module TotalHoareLogic (HD: HoareLogicDefs).
Export HD.
Module HLD:=HD.
Definition sem_wp := wp.
Export Wf.
Fixpoint synt_wp (prog: ImpProg) : Pred -> Pred := fun post e => match prog with | Iskip => post e | (Iset A x expr) => post (E.upd x (E.eval expr e) e) | (Iif cond p1 p2) => ((E.eval cond e)=true -> (synt_wp p1 post e)) /\ ((E.eval cond e)=false -> (synt_wp p2 post e)) | (Iseq p1 p2) => synt_wp p1 (synt_wp p2 post) e | (Iwhile cond p) => exists inv:Pred, exists R:E.Env -> E.Env -> Prop, (well_founded R) /\ (inv e) /\ (forall e', (inv e') -> (E.eval cond e')=false -> post e') /\ (forall e', (inv e') -> (E.eval cond e')=true -> synt_wp p inv e') /\ (forall e0, (inv e0) -> (E.eval cond e0)=true -> synt_wp p (fun e1 => R e1 e0) e0) end.
Hint Resolve synt_wp_monotonic: hoare.
Ltac dec2 n H := case H; clear H; intros n H.
Definition aux_wlp (prog: ImpProg) : Pred -> Pred := fun post e => match prog with | Iskip => post e | (Iset A x expr) => post (E.upd x (E.eval expr e) e) | (Iif cond p1 p2) => forall e', exec e (if E.eval cond e then p1 else p2) e' -> post e' | (Iseq p1 p2) => forall e1 e2, exec e p1 e1 -> exec e1 p2 e2 -> post e2 | (Iwhile cond p) => forall e', exec e (Iif cond (Iseq p (Iwhile cond p)) Iskip) e' -> post e' end.
Ltac exec_inversion H := match type of H with | (exec ?e ?p ?e') => pattern e'; apply (exec_inversion H); simpl; clear H end.
Definition reduces cond p e1 e0 := (E.eval cond e0)=true /\ (exec e0 p e1) /\ exists ef, (exec e1 (Iwhile cond p) ef).
Inductive execn: nat -> E.Env -> ImpProg -> E.Env -> Prop := | execn_Iskip: forall e, (execn 0 e Iskip e) | execn_Iset: forall (A:Type) e x (expr: E.Expr A), (execn 0 e (Iset x expr) (E.upd x (E.eval expr e) e)) | execn_Iif: forall n e (cond: E.Expr bool) p1 p2 e', (execn n e (if (E.eval cond e) then p1 else p2) e') -> (execn n e (Iif cond p1 p2) e') | execn_Iseq: forall n e p1 p2 e' e'', (exec e p1 e') -> (execn n e' p2 e'') -> (execn n e (Iseq p1 p2) e'') | execn_Iwhile: forall n e cond p e', (execn n e (Iif cond (Iseq p (Iwhile cond p)) Iskip) e') -> (execn (S n) e (Iwhile cond p) e').
Hint Resolve execn_Iskip execn_Iset execn_Iif execn_Iseq execn_Iwhile: hoare.
Hint Resolve reduces_wf: hoare.
Hint Resolve wp_complete wp_sound: hoare.
End TotalHoareLogic.

Lemma exec_execn: forall ei p ef, (exec ei p ef) -> (exists n, execn n ei p ef).
Proof.
induction 1; firstorder (eauto with hoare).

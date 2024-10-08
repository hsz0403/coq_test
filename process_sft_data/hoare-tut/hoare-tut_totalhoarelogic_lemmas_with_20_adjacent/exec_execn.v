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

Lemma synt_wp_monotonic: forall (p: ImpProg) (post1 post2: Pred), (forall e, post1 e -> post2 e) -> forall e, (synt_wp p post1 e) -> (synt_wp p post2 e).
Proof.
Admitted.

Lemma synt_wp_conj: forall (p: ImpProg) (post1 post2: Pred) e, (synt_wp p post1 e) -> (synt_wp p post2 e) -> (synt_wp p (fun e => post1 e /\ post2 e) e).
Proof.
induction p; simpl; try ((intuition auto); fail).
intros post1 post2 e H1 H2.
intros; eapply synt_wp_monotonic.
2: apply (IHp1 _ _ _ H1 H2).
simpl; intuition auto.
intros post1 post2 e H1 H2.
dec2 inv1 H1.
dec2 R1 H1.
dec2 inv2 H2.
intros; constructor 1 with (x:=fun e => inv1 e /\ inv2 e).
constructor 1 with (x:=R1).
Admitted.

Lemma wp_sound: forall prog post, synt_wp prog post |= prog [=post=].
Proof.
unfold wp.
induction prog; simpl; try ((intuition eauto with hoare); fail).
intros post e.
set (b:=E.eval cond e).
cut (E.eval cond e=b); auto.
case b; firstorder eauto with hoare.
intros post e H; case (IHprog1 _ _ H).
intros e0 H0; case (IHprog2 post e0); firstorder eauto with hoare.
intros post e H.
dec2 inv H.
dec2 R H.
dec2 Rwf H.
dec2 Hinv H.
dec2 H1 H.
dec2 H2 H.
generalize Hinv.
pattern e.
eapply well_founded_ind; eauto.
clear Hinv e.
intros e' X H'.
set (b:=E.eval cond e').
cut (E.eval cond e'=b); auto.
case b; [ idtac | firstorder eauto with hoare ].
intros H5.
case (IHprog (wp (Iwhile cond prog) post) e'); [ idtac | (unfold wp; firstorder eauto with hoare) ].
eapply synt_wp_monotonic.
2:apply (synt_wp_conj _ _ _ _ (H2 _ H' H5) (H _ H' H5)).
Admitted.

Lemma exec_inversion: forall prog e e', (exec e prog e') -> forall post, (aux_wlp prog post e) -> post e'.
Proof.
Admitted.

Lemma exec_test_inversion: forall A (x:E.Var A) expr e e', (exec e (Iset x expr) e') -> e'=(E.upd x (E.eval expr e) e).
Proof.
intros A x expr e e' H.
Admitted.

Lemma exec_deterministic: forall ei p ef, (exec ei p ef) -> forall ef', (exec ei p ef') -> ef=ef'.
Proof.
induction 1; intros ef' X; exec_inversion X; eauto.
intros e1 e2 X1 X2; assert (X3: e'=e1); auto.
Admitted.

Lemma reduces_wf: forall cond p, well_founded (reduces cond p).
Proof.
unfold well_founded.
intros cond p e0; apply Acc_intro.
intros e1 H; unfold reduces in H.
decompose [ex and] H; clear H.
clear H2 H0 e0.
case (exec_execn H1).
intros n.
generalize cond p e1 x; clear cond p e1 x H1.
elim n.
intros cond p e0 e1 H; inversion_clear H.
clear n; intros n HR cond p e0 e1 H.
inversion_clear H.
inversion_clear H0.
set (b:=E.eval cond e0) in * |-.
cut (E.eval cond e0=b); auto.
generalize H; clear H; case b; simpl.
intros H; inversion_clear H.
intros; apply Acc_intro.
intros e2 H3; unfold reduces in H3.
intuition.
rewrite (exec_deterministic H3 H0); eauto.
intros H H0; apply Acc_intro.
unfold reduces; rewrite H0.
intuition.
Admitted.

Lemma wp_complete: forall prog post, prog [= post =] |= (synt_wp prog post).
Proof.
unfold wp.
intros prog post e H; case H; clear H.
intros e' H; case H; clear H.
generalize post e e'; clear post e e'; elim prog; clear prog; simpl.
intros post e e' H; exec_inversion H; auto.
intros A v expr post e e' H; exec_inversion H; auto.
intros cond p1 Hp1 p2 Hp2 post e e' H; exec_inversion H.
case (E.eval cond e); simpl; firstorder auto || discriminate.
intros p1 Hp1 p2 Hp2 post e e' H.
exec_inversion H.
eauto.
intros cond p Hp post e e' H H0.
constructor 1 with (x:=wp (Iwhile cond p) post).
constructor 1 with (x:=reduces cond p).
Admitted.

Theorem soundness: forall pre p post, pre |= (synt_wp p post) -> pre |= p [=post=].
Proof.
Admitted.

Theorem completeness: forall pre p post, pre |= p [=post=] -> pre |= (synt_wp p post).
Proof.
Admitted.

Lemma exec_execn: forall ei p ef, (exec ei p ef) -> (exists n, execn n ei p ef).
Proof.
induction 1; firstorder (eauto with hoare).

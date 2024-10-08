Global Set Asymmetric Patterns.
Set Implicit Arguments.
Require Export hoarelogicsemantics.
Module PartialHoareLogic (HD: HoareLogicDefs).
Export HD.
Module HLD:=HD.
Definition sem_wp := wlp.
Fixpoint synt_wp (prog: ImpProg) : Pred -> Pred := fun post e => match prog with | Iskip => post e | (Iset A x expr) => post (E.upd x (E.eval expr e) e) | (Iif cond p1 p2) => ((E.eval cond e)=true -> (synt_wp p1 post e)) /\ ((E.eval cond e)=false -> (synt_wp p2 post e)) | (Iseq p1 p2) => synt_wp p1 (synt_wp p2 post) e | (Iwhile cond p) => exists inv:Pred, (inv e) /\ (forall e', (inv e') -> (E.eval cond e')=false -> (post e')) /\ (forall e', (inv e') -> (E.eval cond e')=true -> (synt_wp p inv e')) end.
Hint Resolve synt_wp_monotonic: hoare.
Hint Resolve wp_complete wp_sound: hoare.
End PartialHoareLogic.

Lemma synt_wp_monotonic: forall (p: ImpProg) (post1 post2: Pred), (post1 |= post2) -> (synt_wp p post1) |= (synt_wp p post2).
Proof.
Admitted.

Lemma wp_complete: forall prog post, prog{=post=} |= (synt_wp prog post).
Proof.
unfold wlp; intros prog; elim prog; clear prog; simpl; try ((firstorder auto with hoare); fail).
eauto with hoare.
intros.
constructor 1 with (x:=wlp (Iwhile cond p) post).
Admitted.

Theorem soundness: forall pre p post, pre |= (synt_wp p post) -> pre |= p {=post=}.
Proof.
Admitted.

Theorem completeness: forall pre p post, pre |= p {=post=} -> pre |= (synt_wp p post).
Proof.
Admitted.

Lemma wp_sound: forall prog post, synt_wp prog post |= prog{=post=}.
Proof.
intros prog post e H0 e' H; generalize post H0; clear H0 post.
elim H; clear H e' e prog; simpl; try ((firstorder eauto 20 with hoare); fail).
intros e cond p1 p2 e'.
case (E.eval cond e); simpl; firstorder auto.

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

Lemma wp_complete: forall prog post, prog{=post=} |= (synt_wp prog post).
Proof.
unfold wlp; intros prog; elim prog; clear prog; simpl; try ((firstorder auto with hoare); fail).
eauto with hoare.
intros.
constructor 1 with (x:=wlp (Iwhile cond p) post).
unfold wlp; intuition eauto 20 with hoare.

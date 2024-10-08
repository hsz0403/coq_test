Require Export Monotonicity.
Require Import KLR.
Class Transport {A B} (R: rel A B) (a: A) (b: B) (PA: Prop) (PB: Prop) := transport: R a b -> PA -> PB.
Global Instance prod_rel_transport_eq_pair {A1 B1 A2 B2} (R1: rel A1 B1) (R2: rel A2 B2) x y a1 a2: Transport (prod_rel R1 R2) x y (x = (a1, a2)) (exists b1 b2, y = (b1, b2) /\ R1 a1 b1 /\ R2 a2 b2).
Proof.
intros [Hxy1 Hxy2] Hx.
destruct y.
subst.
simpl in *.
eauto.
Ltac set_le_transport keyword := lazymatch goal with | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB => lazymatch PA with | context [keyword] => let Xv := fresh "X" in evar (Xv: Type); let X := eval red in Xv in clear Xv; unify B (X -> Prop); eapply set_le_transport end end.
Ltac rel_curry_set_le_transport keyword := lazymatch goal with | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB => lazymatch PA with | context [keyword] => let Xv := fresh "X" in evar (Xv: Type); let X := eval red in Xv in clear Xv; let Yv := fresh "Y" in evar (Yv: Type); let Y := eval red in Yv in clear Yv; unify B (X -> Y -> Prop); eapply rel_curry_set_le_transport end end.
Ltac rel_curry2_set_le_transport keyword := lazymatch goal with | |- @Transport ?A ?B ?R ?a ?b ?PA ?PB => lazymatch PA with | context [keyword] => let Xv := fresh "X" in evar (Xv: Type); let X := eval red in Xv in clear Xv; let Yv := fresh "Y" in evar (Yv: Type); let Y := eval red in Yv in clear Yv; let Zv := fresh "Y" in evar (Yv: Type); let Z := eval red in Yv in clear Yv; unify B (X -> Y -> Z -> Prop); eapply rel_curry2_set_le_transport end end.
Ltac split_hyp H := lazymatch type of H with | ex _ => destruct H as [? H]; split_hyp H | _ /\ _ => let H1 := fresh in let H2 := fresh in destruct H as [H1 H2]; split_hyp H1; split_hyp H2 | prod_rel ?Rx ?Ry (?x1, ?y1) (?x2, ?y2) => change (Rx x1 x2 /\ Ry y1 y2) in H; split_hyp H | rel_incr ?acc ?R ?w ?x ?y => let w' := fresh w "'" in let Hw' := fresh "H" w' in destruct H as (w' & Hw' & H); split_hyp H | klr_diam ?l ?R ?w ?x ?y => let w' := fresh w "'" in let Hw' := fresh "H" w' in destruct H as (w' & Hw' & H); split_hyp H | prod_klr ?Rx ?Ry ?w (?x1, ?y1) (?x2, ?y2) => change (Rx w x1 x2 /\ Ry w y1 y2) in H; split_hyp H | _ => idtac end.
Ltac split_hyps := repeat lazymatch goal with | H: ex _ |- _ => destruct H | H: _ /\ _ |- _ => destruct H | H: prod_rel ?Rx ?Ry (?x1, ?y1) (?x2, ?y2) |- _ => change (Rx x1 x2 /\ Ry y1 y2) in H | H: klr_diam ?R ?w ?x ?y |- _ => let w' := fresh w "'" in let Hw' := fresh "H" w' in destruct H as (w' & Hw' & H) | H: prod_klr ?Rx ?Ry ?w (?x1, ?y1) (?x2, ?y2) |- _ => change (Rx w x1 x2 /\ Ry w y1 y2) in H end.
Ltac transport H := revert H; lazymatch goal with | |- ?PA -> ?Q => apply (transport_in_goal (PA:=PA) Q) end; intro H; split_hyp H.
Ltac transport_hyps := repeat match goal with | H: _ |- _ => transport H end.

Lemma set_le_transport {A B} (R: rel A B) sA sB a: Transport (set_le R) sA sB (sA a) (exists b, sB b /\ R a b).
Proof.
intros HsAB Ha.
Admitted.

Lemma rel_curry_set_le_transport {A1 A2 B1 B2} R sA sB (a1: A1) (a2: A2): Transport (% set_le R) sA sB (sA a1 a2) (exists (b1: B1) (b2: B2), sB b1 b2 /\ R (a1, a2) (b1, b2)).
Proof.
intros HsAB Ha.
Admitted.

Lemma impl_transport P Q: Transport impl P Q P Q.
Proof.
Admitted.

Lemma transport_in_goal `{Transport} `{!RAuto (R a b)} `{!Unconvertible a b}: forall (Q: Prop), (PB -> Q) -> (PA -> Q).
Proof.
Admitted.

Lemma rel_curry2_set_le_transport {A1 A2 A3 B1 B2 B3} R sA sB (a1: A1) (a2: A2) (a3: A3): Transport (% % set_le R) sA sB (sA a1 a2 a3) (exists (b1: B1) (b2: B2) (b3: B3), sB b1 b2 b3 /\ R (a1, a2, a3) (b1, b2, b3)).
Proof.
intros HsAB Ha.
destruct (HsAB (a1, a2, a3)) as ([[b1 b2] b3] & Hb & Hab); eauto.

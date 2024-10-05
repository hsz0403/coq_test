Require Import List.
Require Import LetP.
Require Import Relation_Definitions.
Section Reduce.
Variable poly : Set.
Variable cb : list poly -> poly -> Prop.
Variable divp : poly -> poly -> Prop.
Variable reduce : list poly -> poly -> poly -> Prop.
Variable nf : list poly -> poly -> poly.
Variable stable : list poly -> list poly -> Prop.
Variable grobner : list poly -> Prop.
Variable zero : poly.
Variable zerop : poly -> Prop.
Variable zerop_dec : forall p : poly, {zerop p} + {~ zerop p}.
Hypothesis cb_id : forall (L : list poly) (p : poly), In p L -> cb L p.
Hypothesis cb_zerop : forall (L : list poly) (p : poly), zerop p -> cb L p.
Hypothesis cb_incl : forall (L1 L2 : list poly) (p : poly), incl L1 L2 -> cb L1 p -> cb L2 p.
Hypothesis nf_cb : forall (p : poly) (L : list poly), cb (p :: L) (nf L p).
Hypothesis cb_trans : forall (L : list poly) (p q : poly), cb (p :: L) q -> cb L p -> cb L q.
Hypothesis cb_comp : forall L1 L2 : list poly, (forall p : poly, In p L1 -> cb L2 p) -> forall q : poly, cb L1 q -> cb L2 q.
Hypothesis cb_nf : forall (p : poly) (L : list poly), cb (nf L p :: L) p.
Hypothesis cb_compo : forall (p : poly) (L1 : list poly), cb L1 p -> forall L2 : list poly, (forall q : poly, In q L1 -> cb L2 q) -> cb L2 p.
Hypothesis zerop_elim_cb : forall (L : list poly) (p q : poly), zerop p -> cb (p :: L) q -> cb L q.
Hypothesis grobner_def : forall L : list poly, grobner L -> forall p : poly, cb L p -> zerop p \/ (exists q : poly, reduce L p q).
Hypothesis def_grobner : forall L : list poly, (forall p : poly, cb L p -> zerop p \/ (exists q : poly, reduce L p q)) -> grobner L.
Hypothesis nf_div : forall (p : poly) (L : list poly), ~ zerop p -> ~ zerop (nf L p) -> exists q : poly, In q (nf L p :: L) /\ divp p q /\ ~ zerop q.
Hypothesis div_reduce : forall (p : poly) (L1 L2 : list poly), (forall r1 : poly, In r1 L1 -> ~ zerop r1 -> exists r2 : poly, In r2 L2 /\ divp r1 r2) -> forall q : poly, reduce L1 p q -> exists r : poly, reduce L2 p r.
Hypothesis divp_id : forall p : poly, divp p p.
Hypothesis divp_trans : transitive poly divp.
Hypothesis nf_div_zero : forall (p : poly) (L : list poly), ~ zerop p -> zerop (nf L p) -> exists q : poly, In q L /\ divp p q /\ ~ zerop q.
Hint Resolve zerop_nf_cb : core.
Definition redacc : list poly -> list poly -> list poly.
intros H'; elim H'.
intros L; exact (nil (A:=poly)).
intros a p Rec Acc.
apply LetP with (A := poly) (h := nf (p ++ Acc) a).
intros u H'0; case (zerop_dec u); intros Z.
exact (Rec Acc).
exact (u :: Rec (u :: Acc)).
Defined.
Definition red (L : list poly) : list poly := redacc L nil.
Hint Resolve incl_refl incl_tl incl_appr incl_appl incl_cons incl_app in_or_app : core.
Hypothesis nf_div_zero1 : forall (p : poly) (L : list poly), ~ zerop p -> zerop (nf L p) -> ex (fun q : poly => In q L /\ divp p q /\ ~ zerop q).
End Reduce.

Theorem redacc_divp : forall (L1 L2 : list poly) (p : poly), ~ zerop p -> In p (L1 ++ L2) -> exists q : poly, In q (redacc L1 L2 ++ L2) /\ divp p q /\ ~ zerop q.
intros L1; elim L1; simpl in |- *; auto.
intros L2 p H' H'0; exists p; split; auto.
unfold LetP in |- *.
intros a l H' L2 p H'0 H'1; case H'1; [ intros H'2; rewrite <- H'2; clear H'1 | intros H'2; clear H'1 ]; auto.
case (zerop_dec (nf (l ++ L2) a)); simpl in |- *; auto.
intros Z1.
lapply (nf_div_zero1 a (l ++ L2)); [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ]; auto.
case H'6; intros q E; case E; intros H'3 H'4; case H'4; intros H'5 H'7; clear H'4 E H'6.
lapply (H' L2 q); [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ]; auto.
case H'9; intros q0 E; case E; intros H'4 H'6; case H'6; intros H'8 H'10; clear H'6 E H'9.
exists q0; split; [ idtac | split ]; auto.
apply divp_trans with (y := q); auto.
rewrite H'2; auto.
intros Z1.
lapply (nf_div a (l ++ L2)); [ intros H'5; lapply H'5; [ intros H'6; clear H'5 | clear H'5 ] | idtac ]; auto.
case H'6; intros q E; case E; intros H'3 H'4; case H'4; intros H'5 H'7; clear H'4 E H'6.
simpl in H'3.
case H'3; [ intros H'4; clear H'3 | intros H'4; clear H'3 ].
exists q; split; [ idtac | split ]; auto.
lapply (H' (nf (l ++ L2) a :: L2) q); [ intros H'8; lapply H'8; [ intros H'9; clear H'8 | clear H'8 ] | idtac ]; auto.
case H'9; intros q0 E; case E; intros H'3 H'6; case H'6; intros H'8 H'10; clear H'6 E H'9.
exists q0; split; [ idtac | split ]; auto.
case (in_app_or (redacc l (nf (l ++ L2) a :: L2)) (nf (l ++ L2) a :: L2) q0 H'3); auto.
simpl in |- *; auto.
intros H'6; case H'6; [ intros H'9; clear H'6 | intros H'9; clear H'6 ]; auto.
apply divp_trans with (y := q); auto.
case (in_app_or l L2 q H'4); auto with datatypes.
rewrite H'2; auto.
case (zerop_dec (nf (l ++ L2) a)); simpl in |- *; auto.
intros Z1.
case (in_app_or l L2 p H'2); auto.
intros H'3.
lapply (H' (nf (l ++ L2) a :: L2) p); [ intros H'6; lapply H'6; [ intros H'7; clear H'6 | clear H'6 ] | idtac ]; auto.
case H'7; intros q E; case E; intros H'4 H'5; case H'5; intros H'6 H'8; clear H'5 E H'7.
exists q; split; auto.
case (in_app_or (redacc l (nf (l ++ L2) a :: L2)) (nf (l ++ L2) a :: L2) q H'4); auto.
simpl in |- *; auto.
intros H; case H; intros H1; auto.
intros H; exists p; split; [ right | idtac ]; auto.

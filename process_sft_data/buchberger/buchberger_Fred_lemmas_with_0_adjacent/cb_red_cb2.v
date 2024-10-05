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

Theorem cb_red_cb2 : forall (p : poly) (L : list poly), cb (red L) p -> cb L p.
intros p L H'.
apply cb_compo with (L1 := red L); auto.
intros q H'0.
apply red_cb; auto.

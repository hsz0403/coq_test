Require Import List Arith Bool Lia Eqdep_dec.
From Undecidability.Shared.Libs.DLW.Utils Require Import utils_tac utils_list utils_nat finite.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.TRAKHTENBROT Require Import notations utils fol_ops fo_sig fo_terms fo_logic fo_sat decidable.
Set Implicit Arguments.
Local Notation ø := vec_nil.
Section FSAT_ext.
Variable (Σ : fo_signature) (X : Type) (P Q : X -> Prop) (HPQ : forall x, P x <-> Q x) (HP : forall x (H1 H2 : P x), H1 = H2) (HQ : forall x (H1 H2 : Q x), H1 = H2) (M : fo_model Σ (sig P)) (Mdec : fo_model_dec M) (Mfin : finite_t (sig P)).
Let f : sig P -> sig Q.
Proof.
intros (x & Hx); exists x; apply HPQ; auto.
Defined.
Let g : sig Q -> sig P.
Proof.
intros (x & Hx); exists x; apply HPQ; auto.
Defined.
Let Hfg : forall x, f (g x) = x.
Proof.
intros (x & Hx).
unfold f, g; simpl; f_equal; apply HQ.
Let Hgf : forall x, g (f x) = x.
Proof.
intros (x & Hx).
unfold f, g; simpl; f_equal; apply HP.
Let sigQ_fin : finite_t (sig Q).
Proof.
revert Mfin.
apply finite_t_map with (f := f).
intros y; exists (g y); auto.
Let M' : fo_model Σ (sig Q).
Proof.
split.
+
intros s v.
apply f, (fom_syms M s), (vec_map g v).
+
intros r v.
apply (fom_rels M r (vec_map g v)).
Defined.
Let M'_dec : fo_model_dec M'.
Proof.
intros r v; simpl; apply Mdec.
Variable (A : fol_form Σ).
Let ls := fol_syms A.
Let lr := fol_rels A.
Let p : @fo_projection Σ ls lr _ M _ M'.
Proof.
exists f g; auto.
+
intros s v _; simpl; do 2 f_equal.
apply vec_pos_ext; intro; rew vec.
+
intros r v _; simpl.
apply fol_equiv_ext; f_equal.
apply vec_pos_ext; intro; rew vec.
Defined.
Variables (phi : nat -> sig P) (HA : fol_sem M phi A).
Local Theorem fo_form_fin_dec_SAT_in_ext : @fo_form_fin_dec_SAT_in Σ A (sig (fun x => Q x)).
Proof.
exists M', sigQ_fin, M'_dec, (fun n => f (phi n)).
revert HA.
apply fo_model_projection with (p := p).
+
intros; simpl; auto.
+
apply incl_refl.
+
apply incl_refl.
End FSAT_ext.
Section enum_models.
Variables (Σ : fo_signature) (HΣ1 : discrete (syms Σ)) (HΣ2 : discrete (rels Σ)) (X : Type) (HX1 : finite_t X) (HX2 : discrete X) (x : X) (ls : list (syms Σ)) (lr : list (rels Σ)) (ln : list nat).
Let funs := (forall s, vec X (ar_syms Σ s) -> X).
Let Rs : funs -> funs -> Prop.
Proof.
intros s1 s2.
exact ( (forall s, In s ls -> forall v, s1 s v = s2 s v) ).
Defined.
Let finite_t_funs : finite_t_upto funs Rs.
Proof.
apply finite_t_model; auto.
Let rels := { r : forall s, vec X (ar_rels Σ s) -> Prop & forall s v, decidable (r s v) }.
Let Rr : rels -> rels -> Prop.
Proof.
intros (r1 & ?) (r2 & ?).
exact ( (forall r, In r lr -> forall v, @r1 r v <-> r2 r v) ).
Defined.
Hint Resolve finite_t_bool : core.
Let bool_prop (f : forall r, vec X (ar_rels Σ r) -> bool) : rels.
Proof.
exists (fun r v => f r v = true).
intros; apply bool_dec.
Defined.
Let finite_t_rels : finite_t_upto rels Rr.
Proof.
destruct finite_t_model with (ar := ar_rels Σ) (X := X) (Y := bool) (ls := lr) as (l & Hl) ; auto.
{
exact true.
}
exists (map bool_prop l).
intros (f & Hf).
set (g := fun r v => if Hf r v then true else false).
destruct (Hl g) as (g' & H1 & H2).
exists (bool_prop g'); split.
+
apply in_map_iff; exists g'; auto.
+
simpl; intros r Hr v.
rewrite <- H2; auto.
unfold g.
destruct (Hf r v); split; auto; discriminate.
Let model := { M : fo_model Σ X & { _ : nat -> X & fo_model_dec M } }.
Local Definition FO_model_equiv : model -> model -> Prop.
Proof.
intros ((s1,r1) & rho1 & H1 ) ((s2,r2) & rho2 & H2).
exact ( (forall s, In s ls -> forall v, s1 s v = s2 s v) /\ (forall r, In r lr -> forall v, @r1 r v <-> r2 r v) /\ (forall n, In n ln -> rho1 n = rho2 n) ).
Defined.
Let combine : (funs * rels * (nat -> X)) -> model.
Proof.
intros ((f,(g & Hg)),rho).
exists {| fom_syms := f; fom_rels := g |}, rho; auto.
Defined.
Local Theorem finite_t_model_upto : finite_t_upto _ FO_model_equiv.
Proof.
destruct finite_t_funs as (lf & H1).
destruct finite_t_rels as (lg & H2).
destruct finite_t_valuations with X ln as (lrho & H3); auto.
exists (map combine (list_prod (list_prod lf lg) lrho)).
intros ((f,g) & rho & Hg).
destruct (H1 f) as (f' & G1 & G2).
destruct (H2 (existT _ g Hg)) as ((g' & Hg') & G3 & G4).
destruct (H3 rho) as (phi & G5 & G6).
exists (existT _ {| fom_syms := f'; fom_rels := g' |} (existT _ phi Hg')); simpl; split.
+
apply in_map_iff.
exists ((f',existT _ g' Hg'),phi); split; auto.
apply list_prod_spec; split; auto.
apply list_prod_spec; simpl; auto.
+
split; auto.
Local Definition FO_sem : model -> fol_form Σ -> Prop.
Proof.
intros (M & rho & _) A.
exact (fol_sem M rho A).
Defined.
End enum_models.
Section FSAT_in_dec.
Variables (Σ : fo_signature) (HΣ1 : discrete (syms Σ)) (HΣ2 : discrete (rels Σ)) (X : Type) (HX1 : finite_t X) (HX2 : discrete X) (A : fol_form Σ).
End FSAT_in_dec.
Section fo_form_fin_discr_dec_SAT_pos.
Variables (Σ : fo_signature) (A : fol_form Σ).
End fo_form_fin_discr_dec_SAT_pos.

Let Rr : rels -> rels -> Prop.
Proof.
intros (r1 & ?) (r2 & ?).
exact ( (forall r, In r lr -> forall v, @r1 r v <-> r2 r v) ).

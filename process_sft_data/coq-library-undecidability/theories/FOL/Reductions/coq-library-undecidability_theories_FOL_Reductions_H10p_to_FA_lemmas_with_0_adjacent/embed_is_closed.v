Require Import Undecidability.Synthetic.Definitions Undecidability.Synthetic.Undecidability.
From Undecidability.FOL.Util Require Import Syntax Syntax_facts FullTarski FullTarski_facts FullDeduction_facts FullDeduction FA_facts.
Require Import Undecidability.FOL.PA.
From Undecidability.H10 Require Import H10p.
Require Import List Lia.
Fixpoint embed_poly p : term := match p with | dp_nat_pfree n => num n | dp_var_pfree k => $k | dp_comp_pfree do_add_pfree a b => (embed_poly a) ⊕ (embed_poly b) | dp_comp_pfree do_mul_pfree a b => (embed_poly a) ⊗ (embed_poly b) end.
Definition embed_problem (E : H10p_PROBLEM) : form := let (a, b) := E in embed_poly a == embed_poly b.
Definition H10p_sem E sigma := dp_eval_pfree sigma (fst E) = dp_eval_pfree sigma (snd E).
Definition poly_bound p := proj1_sig (find_bounded_t (embed_poly p)).
Definition problem_bound (E : H10p_PROBLEM) := let (a, b) := E in proj1_sig (find_bounded (embed_poly a == embed_poly b) ).
Definition embed E := exist_times (problem_bound E) (embed_problem E).
Fact numeral_subst_invariance n rho : subst_term rho (num n) = num n.
Proof.
induction n.
-
reflexivity.
-
cbn.
now rewrite IHn.
Section FA_ext_Model.
Context {D : Type}.
Context {I : interp D}.
Hypothesis ext_model : extensional I.
Hypothesis FA_model : forall ax rho, In ax FA -> rho ⊨ ax.
Notation "'iO'" := (i_func (f:=Zero) (Vector.nil D)) (at level 2) : PA_Notation.
Fact eval_poly sigma p : eval (sigma >> iμ) (embed_poly p) = iμ (dp_eval_pfree sigma p).
Proof.
induction p; cbn.
-
now rewrite eval_num.
-
reflexivity.
-
destruct d; cbn.
+
now rewrite IHp1, IHp2, add_hom.
+
now rewrite IHp1, IHp2, mult_hom.
End FA_ext_Model.
Section FA_Model.
Context {D : Type}.
Context {I : interp D}.
Hypothesis FA_model : forall rho ax, In ax FAeq -> rho ⊨ ax.
Notation "'iO'" := (i_func (f:=Zero) (Vector.nil D)) (at level 2) : PA_Notation.
End FA_Model.
Fact nat_eval_poly (sigma : env nat) p : @eval _ _ _ interp_nat sigma (embed_poly p) = dp_eval_pfree sigma p.
Proof.
induction p; cbn.
-
now rewrite nat_eval_num.
-
reflexivity.
-
destruct d; cbn.
+
now rewrite IHp1, IHp2.
+
now rewrite IHp1, IHp2.

Lemma embed_is_closed E : bounded 0 (embed E).
Proof.
unfold embed.
rewrite exists_close_form.
unfold problem_bound.
destruct E as [a b]; cbn.
apply (proj2_sig (find_bounded _)).

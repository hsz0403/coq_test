From Undecidability.FOL.Util Require Import Syntax Deduction Tarski Kripke.
Inductive syms_func := s_f : bool -> syms_func | s_e.
Instance sig_func : funcs_signature := {| syms := syms_func; ar_syms := fun f => if f then 1 else 0 |}.
Inductive syms_pred := sPr | sQ.
Instance sig_pred : preds_signature := {| preds := syms_pred; ar_preds := fun P => if P then 2 else 0 |}.
Notation "FOL*_prv_intu" := (@prv _ _ falsity_off intu nil).
Notation "FOL*_valid" := (@valid _ _ falsity_off).
Definition FOL_valid := @valid _ _ falsity_on.
Definition FOL_satis := @satis _ _ falsity_on.
Definition FOL_valid_intu := @kvalid _ _ falsity_on.
Definition FOL_satis_intu := @ksatis _ _ falsity_on.
Definition FOL_prv_intu := @prv _ _ falsity_on intu nil.
Definition FOL_prv_class := @prv _ _ falsity_on class nil.
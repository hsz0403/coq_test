Require Import List.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.ILL Require Import ILL CLL ill ill_cll ill_cll_restr.
Theorem rILL_rCLL_cf_PROVABILITY : rILL_cf_PROVABILITY ⪯ rCLL_cf_PROVABILITY.
Proof.
apply reduces_dependent; exists.
intros (Γ,A).
exists (⟦Γ⟧,[A]::nil).
apply S_ill_cll_restr_equiv.
Qed.
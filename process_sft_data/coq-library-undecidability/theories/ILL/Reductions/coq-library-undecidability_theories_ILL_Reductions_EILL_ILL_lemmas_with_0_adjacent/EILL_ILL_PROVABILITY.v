Require Import List.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.ILL Require Import EILL ILL ill eill.

Theorem EILL_ILL_PROVABILITY : EILL_PROVABILITY ⪯ ILL_PROVABILITY.
Proof.
exists (fun p => match p with (Σ,Γ,p) => (map (fun c => !⦑c⦒) Σ ++ map £ Γ,£ p) end).
intros ((?&?)&?); apply G_eill_S_ill_wc.

From Undecidability.Shared.Libs.DLW Require Import utils_tac.
Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.ILL Require Import EILL ILL CLL ILL_undec EILL_CLL ILL_CLL.
Import UndecidabilityNotations.
Local Hint Resolve rILL_rCLL_cf_PROVABILITY EILL_CLL_cf_PROVABILITY : core.

Theorem CLL_cf_undec : undecidable CLL_cf_PROVABILITY.
Proof.
Admitted.

Theorem rCLL_cf_undec : undecidable rCLL_cf_PROVABILITY.
Proof.
undec from rILL_cf_undec; auto.

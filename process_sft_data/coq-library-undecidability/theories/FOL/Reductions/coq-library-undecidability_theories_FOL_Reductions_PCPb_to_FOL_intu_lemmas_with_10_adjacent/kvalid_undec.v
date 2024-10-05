From Undecidability.Synthetic Require Import Definitions DecidabilityFacts EnumerabilityFacts ReducibilityFacts.
From Undecidability.FOL Require Import FOL Util.Kripke Util.Deduction Util.Syntax Util.Tarski PCPb_to_FOL.
From Undecidability.PCP Require Import PCP Reductions.PCPb_iff_dPCPb.
Section kvalidity.
Local Definition BSRS := list (card bool).
Variable R : BSRS.
Context {ff : falsity_flag}.
End kvalidity.

Theorem BPCP_kprv : PCPb R <-> nil ⊢I (F R).
Proof.
rewrite PCPb_iff_dPCPb.
split.
-
apply BPCP_prv'.
-
intros H % ksoundness'.
rewrite <- PCPb_iff_dPCPb.
Admitted.

Theorem BPCP_kvalid : PCPb R <-> kvalid (F R).
Proof.
split.
-
now intros H % BPCP_kprv % ksoundness'.
-
intros H % kvalid_valid.
Admitted.

Theorem BPCP_ksatis R : ~ PCPb R <-> ksatis (¬ F R).
Proof.
split.
-
intros H % (BPCP_satis R).
now apply ksatis_satis.
-
intros (D & M & u & rho & H) H' % (BPCP_kvalid R (ff:=falsity_on)).
apply (H u), (H' D M u).
Admitted.

Theorem kvalid_red : PCPb ⪯ FOL_valid_intu.
Proof.
exists (fun R => F R).
intros R.
Admitted.

Theorem kprv_red : PCPb ⪯ FOL_prv_intu.
Proof.
exists (fun R => F R).
intros R.
Admitted.

Theorem ksatis_red : complement PCPb ⪯ FOL_satis_intu.
Proof.
exists (fun R => ¬ F R).
intros R.
Admitted.

Corollary kvalid_unenum : UA -> ~ enumerable (complement (@kvalid _ _ falsity_on)).
Proof.
intros H.
Admitted.

Corollary kprv_undec : UA -> ~ decidable (@prv _ _ falsity_on intu nil).
Proof.
intros H.
Admitted.

Corollary kprv_unenum : UA -> ~ enumerable (complement (@prv _ _ falsity_on intu nil)).
Proof.
intros H.
Admitted.

Corollary ksatis_undec : UA -> ~ decidable (@ksatis _ _ falsity_on).
Proof.
intros H1 H2 % (dec_red ksatis_red).
Admitted.

Corollary ksatis_enum : UA -> ~ enumerable (@ksatis _ _ falsity_on).
Proof.
Admitted.

Corollary kvalid_undec : UA -> ~ decidable (@kvalid _ _ falsity_on).
Proof.
intros H.
now apply (not_decidable kvalid_red).

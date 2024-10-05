Require Import Undecidability.FOL.Util.Syntax.
Require Import Undecidability.FOL.Util.sig_bin.
Require Import Undecidability.FOL.Util.FullTarski.
Require Import Undecidability.FOL.Util.FullDeduction.
Definition binFOL_valid := @valid _ _ falsity_on.
Definition binFOL_prv_intu := @prv _ _ falsity_on intu nil.
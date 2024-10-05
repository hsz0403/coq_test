From Undecidability.L Require Export LTactics LTerm Functions.Encoding Tactics.Lbeta_nonrefl.
Import L_Notations.
Goal exists t, closed t /\ t == (enc t).
Proof.
destruct (SecondFixedPoint) with ( s := I) as [t [cls_t A]].
Lproc.
exists t.
split.
Lproc.
rewrite <- A at 1.
clear A.
unfold I.
now Lsimpl.

Goal exists t, closed t /\ t == (enc t).
Proof.
destruct (SecondFixedPoint) with ( s := I) as [t [cls_t A]].
Lproc.
exists t.
split.
Lproc.
rewrite <- A at 1.
clear A.
unfold I.
now Lsimpl.

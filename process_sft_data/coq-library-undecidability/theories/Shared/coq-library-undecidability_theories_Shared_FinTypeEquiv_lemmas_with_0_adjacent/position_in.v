From Undecidability.Shared.Libs.PSL Require Import FiniteTypes.
Fixpoint position {X : eqType} (x : X) (l : list X) : option (Fin.t (length l)).
Proof.
induction l.
-
exact None.
-
cbn.
decide (a = x).
+
exact (Some Fin.F1).
+
destruct (position _ x l) as [res | ].
*
exact (Some (Fin.FS res)).
*
exact None.
Defined.

Lemma position_in {X : eqType} (x : X) (l : list X) (H : x el l) : { i | position x l = Some i}.
Proof.
induction l; cbn in *.
-
inv H.
-
decide (a = x).
+
eauto.
+
destruct IHl as [i IH].
firstorder.
rewrite IH.
eauto.

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

Definition posIn {X : eqType} (x : X) (l : list X) (H : x el l) : Fin.t (length l).
Proof.
eapply position_in in H.
destruct (position x l) as [i | ].
exact i.
abstract (exfalso; firstorder congruence).

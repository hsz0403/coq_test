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

Lemma getatIn {X : Type} (l : list X) (i : Fin.t (length l)) : getat l i el l.
Proof.
induction l.
-
inv i.
-
cbn in *.
eapply (Fin.caseS' i); cbn.
eauto.
eauto.

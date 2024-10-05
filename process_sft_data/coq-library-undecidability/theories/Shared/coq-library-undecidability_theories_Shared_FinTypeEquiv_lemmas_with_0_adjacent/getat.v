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

Fixpoint getat {X : Type} (l : list X) (i : Fin.t (length l)) : X.
Proof.
destruct l.
-
inv i.
-
cbn in i.
eapply (Fin.caseS' i (fun _ => X)).
+
exact x.
+
eapply getat.

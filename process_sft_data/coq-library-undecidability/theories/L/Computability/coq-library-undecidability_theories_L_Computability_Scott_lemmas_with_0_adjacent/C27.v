From Undecidability.L.Computability Require Export Fixpoints Decidability Seval.
From Undecidability.L.Functions Require Export Proc Encoding.
Import ARS.ARSNotations L_Notations.
Goal ~ ldec (fun x => closed x /\ converges x).
Proof.
eapply Scott.
-
tauto.
-
intros s t [cls_s [x [Hx lx]]] cls_t t_e_s; split.
+
eassumption.
+
exists x;split;[|Lproc].
now rewrite t_e_s.
-
exists I.
repeat split.
exists I;split.
reflexivity.
Lproc.
-
exists Omega.
repeat split.
intros [_ [x [Hx lx]]].
inv lx.
eapply Omega_diverges.
exact Hx.

Lemma C27 : forall t, closed t -> ~ ldec (fun x => closed x /\ x == t).
Proof.
intros t cls_t H.
cut (ldec (fun x : term => closed x /\ x == t)).
eapply Scott.
-
tauto.
-
intros s t0 [cls_s H0] cls_t0 H1.
split.
assumption.
rewrite H1.
assumption.
-
exists t.
repeat split.
assumption.
assumption.
reflexivity.
-
destruct H.
destruct H.
destruct (H0 I) as [[] [? ?]].
+
destruct H2 as [? ?].
exists Omega.
split.
intros k r.
simpl.
reflexivity.
intros [_ C].
eapply I_neq_Omega.
rewrite C.
auto.
+
exists I.
split.
Lproc.
auto.
-
eassumption.

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

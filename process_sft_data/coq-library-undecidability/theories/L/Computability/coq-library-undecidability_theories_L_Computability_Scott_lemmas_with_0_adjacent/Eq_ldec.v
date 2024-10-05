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

Lemma Eq_ldec : ~ ldec (fun x => exists (s t : term), x = enc (s t) /\ s == t).
Proof.
intros [u [[cls_u lam_u] Hu]].
pose (t := I).
eapply (C27_proc (t := t)).
Lproc.
pose (v := (lam(u ((ext (term_enc)) ((ext app) #0 (ext t)))))).
exists v.
split.
subst v;Lproc.
intros s.
destruct (Hu (ext (s t))) as [b [eq C]].
exists b.
split.
+
subst v.
Lsimpl.
eassumption.
+
destruct b.
*
destruct C as [? [? [eq' ?]]].
apply inj_enc in eq'.
congruence.
*
intros eq'.
apply C.
now repeat eexists.

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

Theorem Scott (M : term -> Prop) : M <=1 closed -> (forall s t, M s -> closed t -> t == s -> M t) -> (exists t1, closed t1 /\ M t1) -> (exists t2, closed t2 /\ ~ M t2) -> ~ ldec M.
Proof.
intros M_cl M_equiv [s1 [cls_s1 Ms1]] [s2 [cls_s2 nMs2]] [u [[cls_u lam_u] Hu]].
pose (x := lam(u #0 (lam s2) (lam s1) I)).
destruct (SecondFixedPoint (s := x)) as [t [cls_t H]].
subst x.
Lproc.
eapply eqTrans with (s := u (enc t) (lam s2) (lam s1) I) in H.
destruct (Hu t) as [[] [R C]].
-
eapply nMs2, M_equiv; eauto.
rewrite <- H,R.
symmetry.
Lrewrite.
LsimplRed.
-
eapply C, M_equiv; eauto.
rewrite <- H,R.
Lrewrite.
LsimplRed.
-
symmetry.
etransitivity.
apply eqStep.
apply step_Lproc;Lproc.
simpl.
now rewrite cls_u,cls_s1,cls_s2.

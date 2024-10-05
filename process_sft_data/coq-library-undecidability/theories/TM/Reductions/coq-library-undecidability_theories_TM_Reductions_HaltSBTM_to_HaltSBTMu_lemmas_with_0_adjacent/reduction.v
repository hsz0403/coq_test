Require Import Undecidability.TM.SBTM.
Require Import Undecidability.Synthetic.Definitions.
Require Import Equations.Equations.
Section fixM.
Variable M : SBTM.
Definition M' : SBTM.
Proof.
exists (1 + num_states M).
intros [q o].
dependent elimination q.
-
destruct (trans M (Fin.F1, o)) as [[[q' w] m] | ].
dependent elimination q'.
+
exact (Some (Fin.F1, w, m)).
+
exact (Some (Fin.FS (Fin.FS t), w, m)).
+
exact (Some (Fin.FS Fin.F1, None, Nmove)).
-
dependent elimination t.
+
exact None.
+
destruct (trans M (Fin.FS t, o)) as [[[q' w] m] | ].
dependent elimination q'.
*
exact (Some (Fin.F1, w, m)).
*
exact (Some (Fin.FS (Fin.FS t0), w, m)).
*
exact (Some (Fin.FS Fin.F1, None, Nmove)).
Defined.
Definition conv_state (q : Fin.t (S (num_states M))) : Fin.t (S (1 + num_states M)).
Proof.
dependent elimination q.
exact Fin.F1.
exact (Fin.FS (Fin.FS t)).
Defined.
End fixM.

Lemma reduction : HaltSBTM ⪯ HaltSBTMu.
Proof.
unshelve eexists.
-
intros [M t].
refine (_, t).
exists (@M' M).
exists (Fin.FS Fin.F1).
split.
eapply spec1.
eapply spec2.
-
intros [M t].
cbn.
split.
+
intros (q' & t' & H).
assert (conv_state M Fin.F1 = Fin.F1) as E by reflexivity.
cbn [Nat.add] in E.
rewrite <- E.
clear E.
revert H.
generalize (@Fin.F1 (num_states M)) at 1 2.
intros q H.
exists t'.
induction H.
*
econstructor.
now eapply spec3.
cbn.
econstructor.
reflexivity.
*
econstructor.
2:eassumption.
now eapply spec4.
+
intros (t' & H).
assert (conv_state M Fin.F1 = Fin.F1) as E by reflexivity.
cbn [Nat.add] in E.
rewrite <- E in H.
clear E.
revert H.
generalize (@Fin.F1 (num_states M)) at 1 3.
intros q H.
remember (conv_state M q) as q_.
induction H in q, Heqq_ |- *; subst.
*
eexists.
econstructor.
eapply spec2 in H.
dependent elimination q.
inversion H.
inversion H.
*
destruct t as [[ls c] rs].
destruct (trans M (q, c)) as [[[q'_ w_] m_] | ] eqn:Et; pose proof (ET := Et).
--
eapply spec4 in Et.
cbn [curr num_states M' Nat.add] in H.
cbn [Nat.add] in Et.
rewrite H in Et.
inversion Et; subst; clear Et.
edestruct IHeval as (? & ? & ?).
reflexivity.
exists x, x0.
econstructor.
exact ET.
eassumption.
--
eapply spec3 in Et.
cbn [curr num_states M' Nat.add] in H.
cbn [Nat.add] in Et.
rewrite H in Et.
inversion Et; subst; clear Et.
exists q, (ls, c, rs).
econstructor 1.
eassumption.
Unshelve.
exact q.
exact t.

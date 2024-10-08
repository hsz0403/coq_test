Require Export RelDefinitions.
Ltac rdestruct H := lazymatch type of H with | ?R ?m ?n => not_evar R; pattern m, n; apply (rdestruct (R:=R) m n H); clear H; Delay.split_conjunction end.
Ltac rinversion_tac H Hm Hn := lazymatch type of H with | ?R ?m ?n => not_evar R; pattern m, n; lazymatch goal with | |- ?Q _ _ => generalize (eq_refl m), (eq_refl n); change ((fun x y => Delay.delayed_goal (x = m -> y = n -> Q x y)) m n); apply (rdestruct (R:=R) m n H); Delay.split_conjunction; intros Hm Hn end end.
Tactic Notation "rinversion" constr(H) "as" ident(Hl) "," ident(Hr) := rinversion_tac H Hl Hr.
Tactic Notation "rinversion" hyp(H) := let Hl := fresh H "l" in let Hr := fresh H "r" in rinversion_tac H Hl Hr.
Tactic Notation "rinversion" constr(H) := let Hl := fresh "Hl" in let Hr := fresh "Hr" in rinversion_tac H Hl Hr.
Ltac rdestruct_assert := lazymatch goal with | |- _ (match ?m with _ => _ end) (match ?n with _ => _ end) => let Tm := type of m in let Tn := type of n in let R := fresh "R" in evar (R: rel Tm Tn); assert (R m n); subst R end.
Definition rdestruct_result {A B} m n (Q: rel A B): rel A B := fun x y => m = x /\ n = y -> Q x y.
Lemma rdestruct_rstep {A B} m n (R: rel A B) P (Q: rel _ _): RAuto (R m n) -> RDestruct R P -> P (rdestruct_result m n Q) -> Q m n.
Proof.
intros Hmn HR H.
firstorder.
Qed.
Ltac use_rdestruct_rstep m n := let H := fresh in intro H; pattern m, n; eapply (rdestruct_rstep m n); [ .. | eexact H].
Hint Extern 40 (RStep _ (_ (match ?m with _=>_ end) (match ?n with _=>_ end))) => use_rdestruct_rstep m n : typeclass_instances.
CoInductive rdestruct_remember := rdestruct_remember_intro.
Ltac rdestruct_remember := lazymatch goal with | _ : rdestruct_remember |- _ => idtac | _ => let H := fresh "Hrdestruct" in pose proof rdestruct_remember_intro as H end.
Ltac rdestruct_forget := lazymatch goal with | H : rdestruct_remember |- _ => clear H | _ => idtac end.
Lemma rdestruct_forget_rintro {A B} m n (Q: rel A B) x y: RIntro (Q x y) (rdestruct_result m n Q) x y.
Proof.
firstorder.
Qed.
Lemma rdestruct_remember_rintro {A B} m n (Q: rel A B) x y: RIntro (m = x -> n = y -> Q x y) (rdestruct_result m n Q) x y.
Proof.
firstorder.
Qed.
Ltac rdestruct_result_rintro := lazymatch goal with | _ : rdestruct_remember |- _ => eapply rdestruct_remember_rintro | _ => eapply rdestruct_forget_rintro end.
Hint Extern 100 (RIntro _ (rdestruct_result _ _ _) _ _) => rdestruct_result_rintro : typeclass_instances.
Ltac default_rdestruct := let m := fresh "m" in let n := fresh "n" in let Hmn := fresh "H" m n in let P := fresh "P" in let H := fresh in intros m n Hmn P H; revert m n Hmn; delayed_conjunction (intros m n Hmn; destruct Hmn; delay); pattern P; eexact H.
Hint Extern 100 (RDestruct _ _) => default_rdestruct : typeclass_instances.
Ltac eq_rdestruct := let m := fresh "m" in let n := fresh "n" in let Hmn := fresh "H" m n in let P := fresh "P" in let H := fresh in intros m n Hmn P H; revert m n Hmn; delayed_conjunction (intros m n Hmn; destruct Hmn; destruct m; delay); pattern P; eexact H.
Hint Extern 99 (RDestruct eq _) => eq_rdestruct : typeclass_instances.
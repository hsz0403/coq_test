Require Export Jordan5.
Open Scope nat_scope.
Definition dec (A:Prop):Set:= {A}+{~A}.
Open Scope nat_scope.

Lemma cF_L1:forall(m:fmap)(x y z:dart), inv_hmap m -> prec_L m one x y -> let x10 := cF_1 m x in let y0 := cA m zero y in let y_1 := cA_1 m one y in let m1:= L m one x y in cF m1 z = if eq_dart_dec y0 z then x else if eq_dart_dec x10 z then y_1 else cF m z.
Proof.
intros.
elim (exd_dec m z).
intro.
rename a into Ez.
generalize (cF_L m one x y z).
elim (eq_dim_dec one zero).
intro.
inversion a.
intros.
generalize (H1 H H0).
clear H1.
elim (eq_dart_dec y (cA_1 m zero z)).
intro.
elim (eq_dart_dec y0 z).
fold m1 in |- *.
tauto.
intros.
elim b0.
unfold y0 in |- *.
rewrite a in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
elim (eq_dart_dec (cA m one x) (cA_1 m zero z)).
fold m1 in |- *.
intros.
elim (eq_dart_dec y0 z).
unfold y0 in |- *.
intro.
elim b0.
rewrite <- a0 in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
elim (eq_dart_dec x10 z).
intros.
unfold y_1 in |- *.
tauto.
intros.
unfold x10 in b1.
elim b1.
unfold cF_1 in |- *.
rewrite a in |- *.
rewrite cA_cA_1 in |- *.
tauto.
tauto.
tauto.
intros.
elim (eq_dart_dec y0 z).
intro.
unfold y0 in a.
elim b1.
rewrite <- a in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
unfold prec_L in H0.
tauto.
elim (eq_dart_dec x10 z).
unfold x10 in |- *.
intros.
unfold cF_1 in a.
elim b0.
rewrite <- a in |- *.
rewrite cA_1_cA in |- *.
tauto.
tauto.
generalize (exd_cA m one x).
unfold prec_L in H0.
tauto.
fold m1 in H1.
fold (cF m z) in H1.
tauto.
intros.
elim (eq_dart_dec y0 z).
intro.
unfold y0 in a.
elim b.
rewrite <- a in |- *.
generalize (exd_cA m zero y).
unfold prec_L in H0.
tauto.
elim (eq_dart_dec x10 z).
unfold x10 in |- *.
intros.
elim b.
rewrite <- a in |- *.
generalize (exd_cF_1 m x).
unfold prec_L in H0.
tauto.
generalize (exd_cF_not_nil m z H).
intro.
assert (inv_hmap m1).
unfold m1 in |- *.
simpl in |- *.
tauto.
assert (~ exd m1 z).
unfold m1 in |- *.
simpl in |- *.
tauto.
generalize (exd_cF_not_nil m1 z H2).
intro.
intros.
generalize (exd_dec m z).
intro.
generalize (exd_dec m1 z).
intro.
generalize (eq_dart_dec (cF m z) nil).
generalize (eq_dart_dec (cF m1 z) nil).
intros.
assert (cF m z = nil).
tauto.
assert (cF m1 z = nil).
tauto.
rewrite H9 in |- *.
tauto.

Require Export Jordan7.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope nat_scope.

Lemma nf_L0L1_V:forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> let x_1 := cA_1 m one x in let y_0 := cA_1 m zero y in let y'0 := cA m zero y' in let x'1 := cA m one x' in let y'0b := cA (L m zero x y) zero y' in let x_1b := cA_1 (L m one x' y') one x in expf m x_1 y -> ~ expf m x' y'0 -> ~ expf (L m one x' y') x_1b y -> ~ expf (L m zero x y) x' y'0b -> False.
Proof.
intros.
elim (eq_dart_dec x y').
intro.
apply (nf_L0L1_VA m x y x' y' H H0 H1 H2 H3 a).
elim (eq_dart_dec y_0 y').
intros.
apply (nf_L0L1_VB m x y x' y' H H0 H1 H2 H3 b a).
intros.
apply (nf_L0L1_VC m x y x' y' H H0 H1 H2 H3 b0 b).

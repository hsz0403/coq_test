Require Export Jordan8.
Open Scope nat_scope.
Open Scope nat_scope.
Open Scope Z_scope.

Theorem nf_L0L1: forall (m:fmap)(x y x' y':dart), let m1:=L (L m zero x y) one x' y' in let m2:=L (L m one x' y') zero x y in inv_hmap m1 -> nf m1 = nf m2.
Proof.
intros.
unfold m1 in |- *.
unfold m2 in |- *.
set (mx := L m zero x y) in |- *.
set (mx' := L m one x' y') in |- *.
unfold nf in |- *.
fold nf in |- *.
set (x_1 := cA_1 m one x) in |- *.
set (y_0 := cA_1 m zero y) in |- *.
set (y'0 := cA m zero y') in |- *.
set (x'1 := cA m one x') in |- *.
assert (nf mx = nf m + (if expf_dec m x_1 y then 1 else -1)).
simpl in |- *.
unfold x_1 in |- *.
tauto.
assert (nf mx' = nf m + (if expf_dec m x' y'0 then 1 else -1)).
simpl in |- *.
fold y'0 in |- *.
tauto.
set (y'0b := cA mx zero y') in |- *.
set (x_1b := cA_1 mx' one x) in |- *.
rewrite H0 in |- *.
rewrite H1 in |- *.
unfold mx in |- *; unfold mx' in |- *.
elim (expf_dec m x_1 y).
elim (expf_dec m x' y'0).
elim (expf_dec (L m zero x y) x' y'0b).
elim (expf_dec (L m one x' y') x_1b y).
intros.
omega.
intros.
elim (nf_L0L1_I m x y x' y' H a1 a0 a b).
elim (expf_dec (L m one x' y')).
intros.
elim (nf_L0L1_II m x y x' y' H a1 a0 b a).
intros.
tauto.
elim (expf_dec (L m zero x y) x' y'0b).
elim (expf_dec (L m one x' y') x_1b y).
intros.
elim (nf_L0L1_III m x y x' y' H a1 b a a0).
intros.
elim (nf_L0L1_IV m x y x' y' H a0 b0 b a).
elim (expf_dec (L m one x' y') x_1b y).
intros.
omega.
intros.
elim (nf_L0L1_V m x y x' y' H a b1 b b0).
elim (expf_dec m x' y'0).
elim (expf_dec (L m one x' y') x_1b y).
elim (expf_dec (L m zero x y) x' y'0b).
intros.
elim (nf_L0L1_VI m x y x' y' H b a1 a a0).
intros.
elim (nf_L0L1_VII m x y x' y' H b0 a0 b a).
elim (expf_dec (L m zero x y) x' y'0b).
intros.
omega.
intros.
elim (nf_L0L1_VIII m x y x' y' H b1 a b b0).
elim (expf_dec (L m zero x y) x' y'0b).
elim (expf_dec (L m one x' y') x_1b y).
intros.
omega.
intros.
elim (nf_L0L1_IX m x y x' y' H b1 b0 a b).
elim (expf_dec (L m one x' y') x_1b y).
intros.
elim (nf_L0L1_X m x y x' y' H b1 b0 b a).
intros.
omega.

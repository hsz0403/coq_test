Require Import List Lia.
Import ListNotations.
Require Import Undecidability.SystemF.SysF Undecidability.SystemF.Autosubst.syntax.
From Undecidability.SystemF.Util Require Import Facts poly_type_facts term_facts typing_facts iipc2_facts sn_facts.
Require Import Undecidability.DiophantineConstraints.H10C.
Require Import ssreflect ssrbool ssrfun.
Set Default Proof Using "Type".
Set Default Goal Selector "!".
Local Arguments nth_error_In {A l n x}.
Local Arguments In_nth_error {A l x}.
Local Arguments Forall_inv {A P a l}.
Local Arguments Forall_inv_tail {A P a l}.
Module SafePolyType.
Local Fixpoint is_safe_poly_arr (n: nat) (t: poly_type) := match t with | poly_var x => n <= x | poly_arr _ t => is_safe_poly_arr n t | poly_abs _ => False end.
Fixpoint is_safe_poly_type (n: nat) (t: poly_type) := if t is poly_abs t then is_safe_poly_type (1+n) t else is_safe_poly_arr n t.
Definition safe_poly_type (n: nat) (ts: list poly_type) (x: nat) := many_poly_abs n (many_poly_arr ts (poly_var (n + x))).
End SafePolyType.
Module Argument.
Import SafePolyType.
Section H10C_SAT_to_SysF_INH.
Variable h10cs : list h10c.
Fixpoint variable_bound (h10cs : list h10c) : nat := match h10cs with | [] => 0 | (h10c_one x) :: h10cs => 1 + x + variable_bound h10cs | (h10c_plus x y z) :: h10cs => 1 + x + y + z + variable_bound h10cs | (h10c_mult x y z) :: h10cs => 1 + x + y + z + variable_bound h10cs end.
Definition δ := variable_bound h10cs.
Definition tt := 0.
Definition ut := 1.
Definition st := 2.
Definition pt := 3.
Definition b1t := 4.
Definition b2t := 5.
Definition b3t := 6.
Definition GammaC := map poly_var (seq 0 7).
Arguments GammaC : simpl never.
Definition dt := 7.
Definition to_d' d (t: poly_type) := poly_arr t (poly_var (d+dt)).
Definition to_d := to_d' 0.
Definition Ut' d t := many_poly_arr [poly_arr (to_d' d t) (poly_var (d+b1t)); poly_arr t (poly_var (d+b2t))] (poly_var (d+ut)).
Definition Ut := Ut' 0.
Definition St' d := fun '(t1, t2, t3) => many_poly_arr [poly_arr (to_d' d t1) (poly_var (d+b1t)); poly_arr (to_d' d t2) (poly_var (d+b2t)); poly_arr (to_d' d t3) (poly_var (d+b3t))] (poly_var (d+st)).
Definition St := St' 0.
Definition Pt' d := fun '(t1, t2, t3) => many_poly_arr [poly_arr (to_d' d t1) (poly_var (d+b1t)); poly_arr (to_d' d t2) (poly_var (d+b2t)); poly_arr (to_d' d t3) (poly_var (d+b3t))] (poly_var (d+pt)).
Definition Pt := Pt' 0.
Definition zt' d := d + 10.
Definition zt := zt' 0.
Definition t_u := poly_abs (many_poly_arr [ Ut' 1 (poly_var 0); (* forall x *) Ut' 1 (poly_var 0); Ut' 1 (poly_var 0); Ut' 1 (poly_var 0); poly_abs (many_poly_arr [ (* exists y *) Ut' 2 (poly_var 0); (* y is in universe *) St' 2 ((poly_var 1), (poly_var (1+ zt' 2)), (poly_var 0)); (* x + 1 = y *) St' 2 ((poly_var 0), (poly_var (0+ zt' 2)), (poly_var 0)); (* y + 0 = 0 *) Pt' 2 ((poly_var 0), (poly_var (0+ zt' 2)), (poly_var (0+ zt' 2))) (* y * 0 = 0*) ] (poly_var (2+tt))) ] (poly_var (1+tt))).
Definition t_s := many_poly_abs 5 (many_poly_arr [ poly_arr (St' 5 ((poly_var 0), (poly_var 3), (poly_var 4))) (poly_var (5+tt)); (* have a + d = e *) Ut' 5 (poly_var 0); Ut' 5 (poly_var 1); Ut' 5 (poly_var 2); Ut' 5 (poly_var 3); Ut' 5 (poly_var 4); (* for a b c d e such that *) St' 5 ((poly_var 0), (poly_var 1), (poly_var 2)); (* a + b = c *) St' 5 ((poly_var 1), (poly_var (1 + zt' 5)), (poly_var 3)); (* b + 1 = d *) St' 5 ((poly_var 2), (poly_var (1 + zt' 5)), (poly_var 4)) (* c + 1 = e *) ] (poly_var (5+tt))).
Definition t_p := many_poly_abs 5 (many_poly_arr [ poly_arr (Pt' 5 ((poly_var 0), (poly_var 3), (poly_var 4))) (poly_var (5+tt)); (* have a * d = e *) Ut' 5 (poly_var 0); Ut' 5 (poly_var 1); Ut' 5 (poly_var 2); Ut' 5 (poly_var 3); Ut' 5 (poly_var 4); (* for a b c d e such that *) Pt' 5 ((poly_var 0), (poly_var 1), (poly_var 2)); (* a * b = c *) St' 5 ((poly_var 1), (poly_var (1 + zt' 5)), (poly_var 3)); (* b + 1 = d *) St' 5 ((poly_var 2), (poly_var 0), (poly_var 4)) (* c + a = e *) ] (poly_var (5+tt))).
Definition h10c_poly_type (c: h10c) : poly_type := match c with | (h10c_one x) => St' δ (poly_var x, poly_var (δ + zt), poly_var (δ+1+zt)) | (h10c_plus x y z) => St' δ (poly_var x, poly_var y, poly_var z) | (h10c_mult x y z) => Pt' δ (poly_var x, poly_var y, poly_var z) end.
Definition t_cs := many_poly_abs δ (many_poly_arr (map (fun x => Ut' δ (poly_var x)) (seq 0 δ) ++ map h10c_poly_type h10cs) (poly_var (δ + tt))).
Definition Gamma0 := [t_u; t_s; t_p; t_cs].
Definition GammaH := Gamma0 ++ (map Ut (map (fun x => poly_var (x + zt)) [0; 1])) ++ (map St [ (poly_var zt, poly_var zt, poly_var zt); (poly_var (1+zt), poly_var zt, poly_var (1+zt)); (poly_var zt, poly_var (1+zt), poly_var (1+zt))]) ++ (map Pt [(poly_var zt, poly_var zt, poly_var zt); (poly_var (1+zt), poly_var zt, poly_var zt)]).
Arguments Gamma0 : simpl never.
Arguments Ut' : simpl never.
Arguments St' : simpl never.
Arguments St : simpl never.
Arguments Pt' : simpl never.
Arguments Pt : simpl never.
Definition encodes_nat (t: poly_type) (n: nat) := iipc2 GammaC (poly_arr (to_d (poly_var (n + zt))) (to_d t)) /\ iipc2 GammaC (poly_arr (to_d t) (to_d (poly_var (n + zt)))).
Definition encodes_sum := fun '(t1, t2, t3) => exists n1 n2 n3, encodes_nat t1 n1 /\ encodes_nat t2 n2 /\ encodes_nat t3 n3 /\ n1 + n2 = n3.
Definition encodes_prod := fun '(t1, t2, t3) => exists n1 n2 n3, encodes_nat t1 n1 /\ encodes_nat t2 n2 /\ encodes_nat t3 n3 /\ n1 * n2 = n3.
Section InverseTransport.
End InverseTransport.
Section Transport.
Variable φ : nat -> nat.
Variable Hφ : forall c, In c h10cs -> h10c_sem c φ.
Fixpoint value_bound (cs: list h10c) : nat := match cs with | [] => 0 | (h10c_one x) :: cs => 1 + φ x + value_bound cs | (h10c_plus x y z) :: cs => 1 + φ x + φ y + φ z + value_bound cs | (h10c_mult x y z) :: cs => 1 + φ x + φ y + φ z + value_bound cs end.
Definition poly_num n := poly_var (n+zt).
Definition GammaU n := map (fun i => Ut (poly_num i)) (seq 0 (1+n)).
Definition GammaS0 n := map (fun i => St (poly_num i, poly_num 0, poly_num i)) (seq 0 (1+n)).
Definition GammaS1 n := map (fun i => St (poly_num i, poly_num 1, poly_num (1+i))) (seq 0 n).
Definition GammaP0 n := map (fun i => Pt (poly_num i, poly_num 0, poly_num 0)) (seq 0 (1+n)).
Definition GammaUSP n := locked (GammaU (S n) ++ (GammaS0 (S n) ++ GammaS1 (S n)) ++ GammaP0 (S n)).
Definition h10cφ_poly_type (c: h10c) : poly_type := match c with | (h10c_one x) => St (poly_num (φ x), poly_num 0, poly_num 1) | (h10c_plus x y z) => St (poly_num (φ x), poly_num (φ y), poly_num (φ z)) | (h10c_mult x y z) => Pt (poly_num (φ x), poly_num (φ y), poly_num (φ z)) end.
Definition Gammaφ := map h10cφ_poly_type h10cs.
Fact GammaUSn {n} : GammaU (S n) = GammaU n ++ [Ut (poly_num (1+n))].
Proof.
by rewrite /GammaU (ltac:(lia) : 1 + S n = (S n) + 1) [seq _ (S n + 1)]seq_app map_app.
Fact GammaS0Sn {n} : GammaS0 (S n) = GammaS0 n ++ [St (poly_num (1+n), poly_num 0, poly_num (1+n))].
Proof.
by rewrite /GammaS0 (ltac:(lia) : 1 + S n = (S n) + 1) [seq _ (S n + 1)]seq_app map_app.
Fact GammaS1Sn {n} : GammaS1 (S n) = GammaS1 n ++ [St (poly_num n, poly_num 1, poly_num (1+n))].
Proof.
by rewrite (ltac:(lia) : S n = n + 1) /GammaS1 seq_app map_app.
Fact GammaP0Sn {n} : GammaP0 (S n) = GammaP0 n ++ [Pt (poly_num (1+n), poly_num 0, poly_num 0)].
Proof.
by rewrite /GammaP0 (ltac:(lia) : 1 + S n = (S n) + 1) [seq _ (S n + 1)]seq_app map_app.
Local Arguments GammaU : simpl never.
Local Arguments GammaS0 : simpl never.
Local Arguments GammaS1 : simpl never.
Local Arguments GammaP0 : simpl never.
Definition ϵ := fold_right (Nat.add) 0 (map φ (seq 0 δ)).
End Transport.
End H10C_SAT_to_SysF_INH.
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma safe_poly_type_eqE {n n' ts ts' x x'} : safe_poly_type n ts x = safe_poly_type n' ts' x' -> n = n' /\ ts = ts' /\ x = x'.
Proof.
elim: n n' x x'.
-
move=> [|?]; last by case: ts.
move=> x x'.
elim: ts ts'.
+
case; last done.
by move=> [].
+
move=> ? ? IH.
case; first done.
by move=> ? ? [] <- /IH [_] [<-] <-.
-
move=> n IH [|n']; first by case: (ts').
move=> x x' [].
have -> : S (n + x) = n + (S x) by lia.
have -> : S (n' + x') = n' + (S x') by lia.
Admitted.

Lemma is_safe_poly_arrE {i t} : is_safe_poly_arr i t -> exists (ts : list poly_type) (x : nat), t = (many_poly_arr ts (poly_var (i+x))).
Proof.
elim: t.
-
move=> /= x *.
exists [], (x-i).
congr poly_var.
by lia.
-
move=> s _ ? IH /= /IH [ts] [x] ->.
by exists (s :: ts), x.
-
Admitted.

Lemma is_safe_poly_typeE {i t} : is_safe_poly_type i t -> exists (n : nat) (ts : list poly_type) (x : nat), t = many_poly_abs n (many_poly_arr ts (poly_var (n + (i + x)))).
Proof.
elim: t i.
-
move=> /= x i *.
exists 0, [], (x-i).
congr poly_var.
by lia.
-
move=> s _ t _ ? /= /is_safe_poly_arrE [ts] [x] ->.
by exists 0, (s :: ts), x.
-
move=> ? IH i /IH [n] [ts] [x] ->.
exists (1+n), ts, x.
move=> /=.
do 4 f_equal.
Admitted.

Lemma typing_safe_poly_typeE {Gamma P n ss x As y} : typing Gamma P (many_poly_abs n (many_poly_arr ss (poly_var (n+x)))) -> typing Gamma (many_argument_app P As) (poly_var y) -> exists (ts : list poly_type) (Qs : list term), x = y /\ As = (map argument_poly_type ts) ++ (map argument_term Qs) /\ n = length ts /\ length ss = length Qs.
Proof.
elim: n P ss x As.
-
move=> P ss x As /=.
elim: ss P As.
+
move=> P [| [?|?] ?].
*
move=> /typing_functional H /H [] ->.
by exists [], [].
*
move=> /= + /typing_many_argument_subterm [?] /typingE [?].
by move=> /typing_functional H [/H].
*
move=> /= + /typing_many_argument_subterm [?] /typingE [?].
by move=> /typing_functional H [_ /H].
+
move=> s ss IH P [| [Q|?] ?] /=.
*
by move=> /typing_functional H /H.
*
move=> + /copy [/IH {}IH].
move=> + /typing_many_argument_subterm [?] /copy [/typingE [?]].
move=> /typing_functional H [/H{H} [<-]] <- ? /IH.
move=> [[| ? ?]] [Qs] [<-] [->] [?] ->; last done.
by exists [], (Q :: Qs).
*
move=> + /typing_many_argument_subterm [?] /typingE [?].
by move=> /typing_functional H [_ /H].
-
move=> n IH P ss x [|A As] /=.
+
by move=> /typing_functional H /H.
+
move: A => [? | s].
*
move=> + /typing_many_argument_subterm [?] /typingE [?].
by move=> /typing_functional H [/H].
*
move=> /typing_ty_app => /(_ s).
rewrite subst_poly_type_many_poly_abs subst_poly_type_many_poly_arr /=.
have ->: S (n + x) = n + S x by lia.
rewrite iter_up_poly_type_poly_type.
move=> /IH {}IH /IH.
move=> [ts] [Qs] [<-] [->] [->].
rewrite map_length.
move=> ->.
Admitted.

Lemma typing_is_safe_environment {Gamma P x} : normal_form P -> typing Gamma P (poly_var x) -> Forall (is_safe_poly_type 0) Gamma -> exists ss y ts Qs, P = many_app (many_ty_app (var y) ts) Qs /\ nth_error Gamma y = Some (safe_poly_type (length ts) ss x) /\ Forall2 (typing Gamma) Qs (map (subst_poly_type (fold_right scons poly_var (rev ts))) ss).
Proof.
case; [ | by move=> > _ /typingE [?] [] | by move=> > _ /typingE [?] []].
move=> {}P /many_argument_appI [y] [As] [-> _].
move=> /copy [/typing_many_argument_subterm [?]].
move=> /copy [/typingE].
move=> + + + /Forall_forall H => /nth_error_In /H{H} /is_safe_poly_typeE.
move=> [n] [ss] [z] -> Hy HyAs.
exists ss, y.
move: (Hy) (HyAs) => /typing_safe_poly_typeE H /H{H}.
move=> [ts] [Qs] [?] [?] [? ?].
exists ts, Qs.
subst x As.
subst n.
constructor; [|constructor].
-
by rewrite many_argument_app_app many_argument_app_map_argument_poly_type many_argument_app_map_argument_term.
-
by move: Hy => /typingE.
-
move: Hy => /typing_many_ty_appI => /(_ ts ltac:(lia)).
move: HyAs.
rewrite many_argument_app_app many_argument_app_map_argument_poly_type.
move: (many_ty_app (var y) _) => {}P.
rewrite subst_poly_type_many_poly_arr many_argument_app_map_argument_term.
move=> /typing_many_app_arguments H /H.
apply.
Admitted.

Corollary iipc2_is_safe_environment {Gamma x} : iipc2 Gamma (poly_var x) -> Forall (is_safe_poly_type 0) Gamma -> exists ss ts, In (safe_poly_type (length ts) ss x) Gamma /\ Forall (iipc2 Gamma) (map (subst_poly_type (fold_right scons poly_var (rev ts))) ss).
Proof.
move=> [P] /typing_normal_form [{}P] [/typing_is_safe_environment H] /H {}H /H.
move=> [ss] [?] [ts] [?] [_] [/nth_error_In ?] /Forall2_typing_Forall_iipc2 ?.
Admitted.

Lemma last_poly_var_safe_poly_type {t n ss x} : t = safe_poly_type n ss x -> last_poly_var t = Some x.
Proof.
move=> ->.
elim: n ss x.
-
move=> + x.
by elim.
-
move=> n /= + ss x.
have ->: S (n + x) = n + S x by lia.
Admitted.

Lemma safe_poly_typeP {n ss x} : is_safe_poly_type 0 (safe_poly_type n ss x).
Proof.
have ->: x = 0 + x by lia.
move: (0) => k.
elim: n k.
-
move=> k.
elim: ss; [move=> /=; by lia | by move=> /= ? [|? ?]].
-
move=> n IH k /=.
have ->: S (n + (k + x)) = n + ((S k) + x) by lia.
Admitted.

Lemma δP : Forall (fun c => match c with | (h10c_one x) => x < δ | (h10c_plus x y z) => x < δ /\ y < δ /\ z < δ | (h10c_mult x y z) => x < δ /\ y < δ /\ z < δ end) h10cs.
Proof.
rewrite /δ.
elim: (h10cs); first by constructor.
move=> c cs IH.
constructor.
-
case: c => /= *; by lia.
-
apply: Forall_impl IH.
Admitted.

Lemma is_safe_environment_Gamma0 : Forall (is_safe_poly_type 0) Gamma0.
Proof.
do 3 (constructor; first by move=> /=; lia).
Admitted.

Lemma is_safe_environment_Ut {ts} : Forall (is_safe_poly_type 0) (map Ut ts).
Proof.
apply /Forall_mapP /Forall_forall => ? _ /=.
Admitted.

Lemma is_safe_environment_St {tSs} : Forall (is_safe_poly_type 0) (map St tSs).
Proof.
apply /Forall_mapP /Forall_forall => [[[? ?] ?]] _ /=.
Admitted.

Lemma is_safe_environment_Pt {tPs} : Forall (is_safe_poly_type 0) (map Pt tPs).
Proof.
apply /Forall_mapP /Forall_forall => [[[? ?] ?]] _ /=.
Admitted.

Lemma iipc2_to_dE {x y: nat} : dt < x -> dt < y -> iipc2 GammaC (poly_arr (to_d (poly_var x)) (to_d (poly_var y))) -> x = y.
Proof.
move=> Hx Hy /iipc2_poly_arrE /iipc2_poly_arrE /iipc2_is_safe_environment.
move=> [:HGamma].
rewrite [GammaC]lock.
apply: unnest.
{
abstract: HGamma.
rewrite -lock.
by do ? (constructor; first by move=> /=; lia).
}
move=> [ss] [ts] /= [].
move=> [| [|]].
-
move=> /last_poly_var_safe_poly_type [].
by lia.
-
have -> : to_d (poly_var x) = safe_poly_type 0 [poly_var x] dt by done.
move=> /safe_poly_type_eqE [+] [<- _].
case: ts; last done.
move=> _ /Forall_inv /iipc2_is_safe_environment => /(_ HGamma).
move=> [ss'] [ts'] /= [].
move=> [| [|]].
+
by move=> /last_poly_var_safe_poly_type [] <-.
+
move=> /safe_poly_type_eqE.
by lia.
+
rewrite -lock /GammaC in_map_iff => [[?]] [+].
move=> /last_poly_var_safe_poly_type [->] /in_seq.
move: Hx.
rewrite /dt.
by lia.
-
rewrite -lock /GammaC.
move=> /in_map_iff [?] [].
move=> /last_poly_var_safe_poly_type [->] /in_seq.
move: Hx.
rewrite /dt.
Admitted.

Lemma to_d_typingI s t Gamma : iipc2 Gamma (poly_arr (poly_arr s t) (poly_arr (to_d t) (to_d s))).
Proof.
eexists.
apply /typing_abs /typing_abs /typing_abs /typing_app.
-
apply: (typing_var (x := 1)).
by reflexivity.
-
apply: typing_app.
+
apply: (typing_var (x := 2)).
by reflexivity.
+
apply: (typing_var (x := 0)).
Admitted.

Lemma encodes_natI (n: nat) : encodes_nat (poly_var (n + zt)) n.
Proof.
Admitted.

Lemma encodes_nat_transport {s t n n'} : iipc2 GammaC (poly_arr (to_d s) (to_d t)) -> encodes_nat s n -> encodes_nat t n' -> n = n'.
Proof.
move=> + [Hn _] [_ Hn'].
move: Hn => /iipc2_poly_arr_comp H /H{H}.
move: Hn' => + /iipc2_poly_arr_comp H => /H{H} /iipc2_to_dE.
rewrite /dt /zt /zt'.
Admitted.

Lemma parameters_poly_arr_safe_poly_type {n ss x}: parameters_poly_arr (safe_poly_type n ss x) = if n is 0 then ss else [].
Proof.
case: n; last done.
elim: ss; first done.
by move=> /= ? ? ->.

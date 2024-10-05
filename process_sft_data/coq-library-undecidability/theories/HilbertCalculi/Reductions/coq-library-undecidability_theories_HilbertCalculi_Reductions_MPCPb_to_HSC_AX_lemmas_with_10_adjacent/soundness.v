Require Import List Lia.
Import ListNotations.
Require Import ssreflect ssrbool ssrfun.
Require Import Undecidability.HilbertCalculi.HSC.
Require Import Undecidability.HilbertCalculi.Util.HSCFacts.
Require Import Undecidability.PCP.PCP.
Set Default Goal Selector "!".
Module Argument.
Local Arguments incl_cons_inv {A a l m}.
Local Arguments incl_cons {A a l m}.
Definition bullet := var 0.
Definition b2 := (arr bullet bullet).
Definition b3 := arr bullet (arr bullet bullet).
Fixpoint append_word (s: formula) (v: list bool) := match v with | [] => s | a :: v => if a then append_word (arr b2 s) v else append_word (arr b3 s) v end.
Definition encode_word (v: list bool) := append_word bullet v.
Definition encode_pair (s t: formula) := arr b3 (arr s (arr t b3)).
Local Notation "⟨ s , t ⟩" := (encode_pair s t).
Local Notation "⟦ v ⟧" := (encode_word v).
Local Notation "s → t" := (arr s t) (at level 50).
Definition Γ v w P := (encode_pair (var 1) (var 1)) :: (arr (encode_pair (encode_word v) (encode_word w)) a_b_a) :: map (fun '(v, w) => arr (encode_pair (append_word (var 2) v) (append_word (var 3) w)) (encode_pair (var 2) (var 3))) ((v, w) :: P).
Definition adequate v w P n := exists p q, der (Γ v w P) n (arr p (arr q p)).
Definition solving (v w: list bool) P n := exists A, (incl A ((v, w) :: P)) /\ exists ζ, der (Γ v w P) n (substitute ζ (encode_pair (encode_word (v ++ tau1 A)) (encode_word (w ++ tau2 A)))).
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma adequate_step {v w P n} : adequate v w P (S n) -> adequate v w P n \/ solving v w P n.
Proof.
move=> [p [q /derE]] => [[ζ [s [k [_]]]]].
rewrite {1}/Γ /In -/(In _ _).
case.
case; last case.
{
move=> ?.
subst s.
case: k.
{
move=> [_] /=.
case=> -> ->.
move=> /(f_equal size) /=.
by lia.
}
move=> k /= [/ForallE] [? _] _.
left.
eexists.
eexists.
by eassumption.
}
{
move=> ?.
subst s.
case: k.
{
move=> [_] /=.
case=> <- _.
case=> _ /(f_equal size) /=.
by lia.
}
move=> k /= [/ForallE] [? _] _.
right.
exists [].
constructor; first done.
eexists.
rewrite ? app_nil_r /=.
by eassumption.
}
{
move /in_map_iff => [[x y] [<- _]] /=.
case: k; last case.
-
move=> [_] /=.
case=> <- _.
case=> _ _ _ /(f_equal size) /=.
by lia.
-
move=> [_] /=.
case=> <- _.
move=> /(f_equal size) /=.
by lia.
-
move=> k /= [/ForallE] [_] /ForallE [? _] _.
left.
eexists.
eexists.
by eassumption.
Admitted.

Lemma solving_step {v w P n} : solving v w P (S n) -> adequate v w P n \/ solving v w P n \/ MPCPb ((v, w), P).
Proof.
move=> [A [HA [ξ /derE]]].
move=> [ζ [s [k [_]]]].
rewrite {1}/Γ /In -/(In _ _).
case.
case; last case.
{
move=> ?.
subst s.
case: k.
{
move=> /= [_].
case=> _ _ _ -> /unify_words HA2 _ _ _.
right.
right.
eexists.
by constructor; eassumption.
}
move=> k /= [/ForallE] [? _] *.
left.
eexists.
eexists.
by eassumption.
}
{
move=> ?.
subst s.
case: k.
{
move=> /= [_].
case=> <- _ /(f_equal size) /=.
by lia.
}
move=> k /= [/ForallE] [? _] *.
right.
left.
exists [].
constructor; first done.
eexists.
move=> /=.
rewrite ? app_nil_r.
by eassumption.
}
{
move /in_map_iff => [[x y]].
move=> [<- ?] /=.
case: k; last case.
-
move=> [_] /=.
case=> -> _ /(f_equal size) /=.
by lia.
-
move=> /= [/ForallE] [H1 _] [] H2.
move: H1.
rewrite H2.
rewrite - ? /(substitute ζ (var _)).
move=> + _ _ /(substitute_combine H2 (x := x)) Hx.
move=> + /(substitute_combine H2 (x := y)) Hy _ _ _.
rewrite Hx Hy => HD.
right.
left.
exists (A ++ [(x, y)]).
constructor.
{
apply: incl_app; first done.
by apply /incl_cons.
}
exists ξ => /=.
by rewrite tau1_lastP tau2_lastP ? app_assoc.
-
move=> k /= [/ForallE] [_ /ForallE] [? _] *.
left.
eexists.
eexists.
by eassumption.
Admitted.

Lemma adequate0E {v w P} : not (adequate v w P 0).
Proof.
Admitted.

Lemma solving0E {v w P} : not (solving v w P 0).
Proof.
Admitted.

Lemma complete_adequacy {v w P n}: adequate v w P n -> MPCPb ((v, w), P).
Proof.
apply: (@proj1 _ (solving v w P n -> MPCPb ((v, w), P))).
elim: n.
{
constructor; [by move /adequate0E | by move /solving0E].
}
move=> n [IH1 IH2].
constructor.
{
by case /adequate_step.
}
Admitted.

Lemma completeness {v w P} : hsc (Γ v w P) a_b_a -> MPCPb ((v, w), P).
Proof.
move /hsc_der => [n ?].
apply: complete_adequacy.
eexists.
eexists.
Admitted.

Lemma transparent_encode_pair {ζ s t} : ζ 0 = var 0 -> substitute ζ (encode_pair s t) = encode_pair (substitute ζ s) (substitute ζ t).
Proof.
Admitted.

Lemma transparent_append_word {ζ s v} : ζ 0 = var 0 -> substitute ζ (append_word s v) = append_word (substitute ζ s) v.
Proof.
move=> Hζ.
elim: v s; first done.
move=> a v IH s.
Admitted.

Lemma substitute_arrP {ζ s t} : substitute ζ (arr s t) = arr (substitute ζ s) (substitute ζ t).
Proof.
Admitted.

Lemma soundness_ind {v w P x y A} : incl A ((v, w) :: P) -> x ++ tau1 A = y ++ tau2 A -> hsc (Γ v w P) (encode_pair (encode_word x) (encode_word y)).
Proof.
elim: A x y.
{
move=> x y _ /=.
rewrite ? app_nil_r => <-.
pose ζ i := if i is 1 then encode_word x else var i.
have -> : encode_pair (encode_word x) (encode_word x) = substitute ζ (encode_pair (var 1) (var 1)) by done.
apply: hsc_var.
rewrite /Γ /In.
by left.
}
move=> [a b] A IH x y /incl_cons_inv [? ?].
rewrite /tau1 -/tau1 /tau2 -/tau2 ? app_assoc.
move /IH => /(_ ltac:(assumption)) ?.
apply: hsc_arr; last eassumption.
rewrite ? encode_word_app.
pose ζ i := if i is 2 then encode_word x else if i is 3 then encode_word y else var i.
have -> : encode_word x = substitute ζ (var 2) by done.
have -> : encode_word y = substitute ζ (var 3) by done.
rewrite - ? transparent_append_word; try done.
rewrite - ? transparent_encode_pair; try done.
rewrite - substitute_arrP.
apply: hsc_var.
rewrite /Γ.
right.
right.
rewrite in_map_iff.
exists (a, b).
Admitted.

Theorem reduction : MPCPb ⪯ HSC_AX.
Proof.
exists (fun '((v, w), P) => exist _ (Argument.Γ v w P) Argument.Γ_allowed).
intros [[v w] P].
constructor.
-
exact Argument.soundness.
-
Admitted.

Lemma soundness {v w P} : MPCPb ((v, w), P) -> hsc (Γ v w P) a_b_a.
Proof.
move=> [A [/soundness_ind + H]] => /(_ _ _ H){H} ?.
apply: hsc_arr; last eassumption.
pose ζ i := var i.
have Hζ: forall s, s = substitute ζ s.
{
elim; first done.
by move=> ? + ? /= => <- <-.
}
rewrite (Hζ (arr _ _)).
apply: hsc_var.
rewrite /Γ.
right.
by left.

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

Lemma arr_allowed {s t} : hsc [a_b_a] t -> hsc [a_b_a] (arr s t).
Proof.
move=> H.
apply: hsc_arr; last by eassumption.
pose ζ i := if i is 0 then t else if i is 1 then s else var i.
have -> : arr t (arr s t) = substitute ζ a_b_a by done.
apply: hsc_var.
Admitted.

Lemma b3_allowed : hsc [a_b_a] b3.
Proof.
pose ζ i := if i is 0 then bullet else if i is 1 then bullet else var i.
have -> : b3 = substitute ζ a_b_a by done.
apply: hsc_var.
Admitted.

Lemma Γ_allowed {v w P} : forall r, In r (Γ v w P) -> hsc [a_b_a] r.
Proof.
apply /Forall_forall.
constructor; [|constructor; [|constructor]].
-
do 3 (apply: arr_allowed).
by apply: b3_allowed.
-
apply: arr_allowed.
have -> : a_b_a = substitute var a_b_a by done.
apply: hsc_var.
by left.
-
do 4 (apply: arr_allowed).
by apply: b3_allowed.
-
apply /Forall_forall => ? /in_map_iff [[x y]] [<- _].
do 4 (apply: arr_allowed).
Admitted.

Lemma encode_word_app {v x} : encode_word (v ++ x) = append_word (encode_word v) x.
Proof.
elim: x v.
{
move=> v.
by rewrite app_nil_r.
}
move=> a x IH v.
rewrite -/(app [a] _) ? app_assoc IH encode_word_last.
Admitted.

Lemma unify_words {v w ζ} : substitute ζ (encode_word v) = substitute ζ (encode_word w) -> v = w.
Proof.
move: v w.
elim /rev_ind.
{
elim /rev_ind; first done.
move=> b w _.
rewrite encode_word_last.
move: b => [] /(f_equal size) /=; by lia.
}
move=> a v IH.
elim /rev_ind.
{
rewrite encode_word_last.
move: a => [] /(f_equal size) /=; by lia.
}
move=> b w _.
rewrite ? encode_word_last.
case: a; case: b; move=> /=; case.
-
by move /IH => ->.
-
move /(f_equal size) => /=.
by lia.
-
move /(f_equal size) => /=.
by lia.
-
Admitted.

Lemma substitute_combine {ζ ξ r v x} : ζ 0 = ξ 0 -> substitute ζ r = substitute ξ (encode_word v) -> substitute ζ (append_word r x) = substitute ξ (encode_word (v ++ x)).
Proof.
move=> ?.
elim: x v r.
{
move=> ?.
by rewrite app_nil_r.
}
move=> a x IH v r /=.
have -> : v ++ a :: x = v ++ [a] ++ x by done.
rewrite app_assoc.
move=> ?.
Admitted.

Lemma tau1_lastP {x y: list bool} {A} : tau1 (A ++ [(x, y)]) = tau1 A ++ x.
Proof.
elim: A; first by rewrite /= app_nil_r.
move=> [a b] A /= ->.
Admitted.

Lemma tau2_lastP {x y: list bool} {A} : tau2 (A ++ [(x, y)]) = tau2 A ++ y.
Proof.
elim: A; first by rewrite /= app_nil_r.
move=> [a b] A /= ->.
Admitted.

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

Lemma encode_word_last {a v} : encode_word (v ++ [a]) = arr (if a then b2 else b3) (encode_word v).
Proof.
rewrite /encode_word.
move: (bullet) => r.
elim: v r.
{
move=> r.
by case: a.
}
move=> b A IH r.
case: b; by apply: IH.

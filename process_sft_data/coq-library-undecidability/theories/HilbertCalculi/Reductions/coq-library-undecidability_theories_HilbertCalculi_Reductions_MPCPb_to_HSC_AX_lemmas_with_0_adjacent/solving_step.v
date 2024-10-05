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
}

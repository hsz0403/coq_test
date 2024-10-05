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
Definition ΓPCP := [ (* ((Q, P), (x, x)) *) encode_pair (var 1) (encode_pair (var 2) (var 2)); (* ((P, P), ((x, v'), (y, w'))) → ((((v', w'), Q), P), ((x, •), (y, •))) *) arr (encode_pair (encode_pair (var 4) (var 4)) (encode_pair (encode_pair (var 5) (var 1)) (encode_pair (var 6) (var 2)))) (encode_pair (encode_pair (encode_pair (encode_pair (var 1) (var 2)) (var 3)) (var 4)) (encode_pair (encode_pair (var 5) bullet) (encode_pair (var 6) bullet))); (* ((Q, P), (x, y)) → ((((v', w'), Q), P), (x, y)) *) arr (encode_pair (encode_pair (var 2) (var 3)) (var 4)) (encode_pair (encode_pair (encode_pair (var 1) (var 2)) (var 3)) (var 4)); (* ((Q, P), ((x, a), v'), y) → ((Q, P), ((x, (a, v')), y) *) arr (encode_pair (var 1) (encode_pair (encode_pair (encode_pair (var 2) (var 3)) (var 4)) (var 5))) (encode_pair (var 1) (encode_pair (encode_pair (var 2) (encode_pair (var 3) (var 4))) (var 5))); (* ((Q, P), (x, ((y, a), w')) → ((Q, P), (x, (y, (a, w'))) *) arr (encode_pair (var 1) (encode_pair (var 5) (encode_pair (encode_pair (var 2) (var 3)) (var 4)))) (encode_pair (var 1) (encode_pair (var 5) (encode_pair (var 2) (encode_pair (var 3) (var 4))))) ].
Definition encode_bool b := if b then b2 else b3.
Fixpoint encode_list {X: Type} (encode_X: X -> formula) (A: list X) : formula := match A with | [] => bullet | a :: A => encode_pair (encode_X a) (encode_list encode_X A) end.
Fixpoint encode_word' (s: formula) (v: list bool) := match v with | [] => s | a :: v => encode_word' (encode_pair s (if a then b2 else b3)) v end.
Definition encode_word_pair '(x, y) := encode_pair (encode_list encode_bool x) (encode_list encode_bool y).
Definition PCPf P x y := encode_pair (encode_pair (encode_list encode_word_pair P) (encode_list encode_word_pair P)) (encode_pair (encode_pair (encode_word' bullet x) bullet) (encode_pair (encode_word' bullet y) bullet)).
Definition PCPf' Q P s t := encode_pair (encode_pair (encode_list encode_word_pair Q) (encode_list encode_word_pair P)) (encode_pair s t).
End Argument.
Require Import Undecidability.Synthetic.Definitions.

Lemma ΓPCP_assoc_y {P r y w} : hsc ΓPCP (PCPf' P P r (encode_pair (encode_word' bullet (y ++ w)) bullet)) -> hsc ΓPCP (PCPf' P P r (encode_pair (encode_word' bullet y) (encode_list encode_bool w))).
Proof.
elim: w y.
{
move=> ?.
by rewrite app_nil_r.
}
move=> a w IH y.
rewrite -/(app [a] _) app_assoc.
move /IH.
rewrite encode_word'_last.
move /(hsc_arr _ _ _ _).
apply.
evar (ζ : nat -> formula).
instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | 2 => _ | 3 => _ | 4 => _ | _ => _ end).
apply: (hscI (ζ := ζ)).
{
rewrite /ΓPCP.
do 4 right.
left.
by reflexivity.
}
Admitted.

Lemma ΓPCP_saturate {Q R P s t} : P = R ++ Q -> hsc ΓPCP (PCPf' Q P s t) -> hsc ΓPCP (PCPf' P P s t).
Proof.
elim /rev_ind : R Q P; first by move=> Q P ->.
move=> vw R IH Q P.
rewrite -app_assoc.
move=> ->.
move=> ?.
suff : hsc ΓPCP (PCPf' ([vw] ++ Q) (R ++ ([vw] ++ Q)) s t) by (move /IH; apply).
apply: hsc_arr; last eassumption.
evar (ζ : nat -> formula).
instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | 2 => _ | 3 => _ | _ => _ end).
apply: (hscI (ζ := ζ)).
{
rewrite /ΓPCP.
do 2 right.
left.
by reflexivity.
}
Admitted.

Lemma ΓPCP_step {P x y v w} : In (v, w) P -> hsc ΓPCP (PCPf' P P (encode_pair (encode_word' bullet x) (encode_list encode_bool v)) (encode_pair (encode_word' bullet y) (encode_list encode_bool w))) -> hsc ΓPCP (PCPf P x y).
Proof.
move /(@in_split _ _) => [R [Q ?]] ?.
have : hsc ΓPCP (PCPf' ((v, w) :: Q) P (encode_pair (encode_word' bullet x) bullet) (encode_pair (encode_word' bullet y) bullet)).
{
apply: hsc_arr; last eassumption.
evar (ζ : nat -> formula).
instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | 2 => _ | 3 => _ | 4 => _ | 5 => _ | _ => _ end).
apply: (hscI (ζ := ζ)).
{
rewrite /ΓPCP.
do 1 right.
left.
by reflexivity.
}
by rewrite /ζ substitute_arrP /PCPf' ? transparent_encode_pair.
}
move /ΓPCP_saturate.
apply.
Admitted.

Lemma ΓPCP_soundness_ind {v w P A} : incl A ((v, w) :: P) -> hsc ΓPCP (PCPf ((v, w) :: P) (v ++ (tau1 A)) (w ++ (tau2 A))) -> hsc ΓPCP (PCPf ((v, w) :: P) v w).
Proof.
elim /rev_ind : A.
{
move=> _ /=.
by rewrite ? app_nil_r.
}
move=> [x y] A IH /incl_app_inv [/IH] + /incl_cons_inv [? _].
rewrite tau1_lastP tau2_lastP ? app_assoc.
move=> + ?; apply.
apply: ΓPCP_step; first by eassumption.
apply: ΓPCP_assoc_x.
apply: ΓPCP_assoc_y.
Admitted.

Lemma ΓPCP_soundness {v w P} : MPCPb ((v, w), P) -> hsc ΓPCP (PCPf ((v, w) :: P) v w).
Proof.
move=> [A [/ΓPCP_soundness_ind]].
move=> + H.
rewrite {}H.
apply.
evar (ζ : nat -> formula).
instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | _ => _ end).
apply: (hscI (ζ := ζ)); first by left.
Admitted.

Lemma encode_bool_injective {a b} : encode_bool a = encode_bool b -> a = b.
Proof.
Admitted.

Lemma encode_word'_injective {x y} : encode_word' bullet x = encode_word' bullet y -> x = y.
Proof.
move: x y.
elim /rev_ind => [|a x IHx].
all: elim /rev_ind => [|b y IHy].
all: rewrite ? encode_word'_last.
all: try done.
Admitted.

Lemma encode_list_injective {x y} : encode_list encode_bool x = encode_list encode_bool y -> x = y.
Proof.
elim: x y=> [|a x IH]; case=> //=.
Admitted.

Lemma substitute_pairP {ζ s t s' t'} : (substitute ζ (encode_pair s t) = encode_pair s' t') <-> ζ 0 = bullet /\ substitute ζ s = s' /\ substitute ζ t = t'.
Proof.
constructor; first by case.
Admitted.

Lemma ΓPCP_completeness_ind {Q P x y v w n} : incl Q P -> der ΓPCP n (PCPf' Q P (encode_pair (encode_word' bullet x) (encode_list encode_bool v)) (encode_pair (encode_word' bullet y) (encode_list encode_bool w))) -> exists A, incl A P /\ x ++ v ++ tau1 A = y ++ w ++ tau2 A.
Proof.
elim: n Q x y v w; first by move=> > _ /der_0E.
move=> n IH Q x y v w HQ /derE.
move=> [ζ [s [k [_ [+ [+]]]]]].
have Hu (r) : r = arr r (arr r r) -> False.
{
move /(f_equal size) => /=.
by lia.
}
rewrite /ΓPCP /In -/ΓPCP.
case; last case; last case; last case; last case; last done.
all: move=> <-.
{
case: k=> [|k] /=; last by move=> /ForallE [/not_ΓPCP_rrr].
move=> _.
case.
do 7 (move=> _).
move=> ->.
case=> /encode_word'_injective + /encode_list_injective.
move=> -> ->.
do 6 (move=> _).
exists [].
by constructor.
}
all: case: k=> [|k].
1,3,5,7: move=> _ /=; case=> <- *; exfalso; apply: Hu; by eassumption.
all: case: k=> [|k].
2,4,6,8: by move=> /= /ForallE [_] /ForallE [/not_ΓPCP_rrr].
all: rewrite substitute_arrP /arguments /target.
all: move=> /ForallE [Hder _]; rewrite ? substitute_pairP.
{
move=> [H0] [[_ [H123 H4]]] [_] [[_ [H5 Hv]]] [_ [H6 Hw]].
move: H123 HQ.
case: Q; first done.
move=> [v' w'] Q.
rewrite /encode_list -/encode_list /encode_word_pair -/encode_word_pair.
rewrite ? substitute_pairP.
move=> [_ [[_ [H1 H2]] H3]].
move: Hder.
rewrite ? transparent_encode_pair //.
rewrite H1 H2 H4 H5 H6.
move /IH.
move /(_ ltac:(done)).
move=> [A [HAP HxyA]].
move /(_ (v', w')).
move /(_ ltac:(by left)) => ?.
move: v w Hv Hw => [|? ?] [|? ?].
{
exists ((v', w') :: A).
constructor; [by apply /incl_cons | by assumption].
}
all: by rewrite /= H0.
}
{
move=> [H0] [[_ [H12 H3]]] H4.
move: H12 HQ.
case: Q; first done.
move=> ? Q.
rewrite /encode_list -/encode_list ? substitute_pairP.
move=> [_ [_ H2]].
move=> /incl_cons_inv [_ HQ].
move: Hder.
rewrite ? transparent_encode_pair => //.
rewrite H2 H3 H4.
move /IH.
by apply.
}
{
move=> [H0] [H1] [_] [[_ [H2]]] H34 H5.
move: H34.
case: v; first done.
move=> a v.
rewrite /encode_list -/encode_list substitute_pairP.
move=> [_ [H3 H4]].
move: Hder.
rewrite ? transparent_encode_pair => //.
rewrite H1 H2 H3 H4 H5 -encode_word'_last.
move /IH.
rewrite -/(app [a] v).
move /(_ ltac:(done)) => [A [?]].
rewrite - ? app_assoc => ?.
by exists A.
}
{
move=> [H0] [H1] [_] [H5] [_ [H2 H34]].
move: H34.
case: w; first done.
move=> a w.
rewrite /encode_list -/encode_list substitute_pairP.
move=> [_ [H3 H4]].
move: Hder.
rewrite ? transparent_encode_pair => //.
rewrite H1 H2 H3 H4 H5 -encode_word'_last.
move /IH.
rewrite -/(app [a] w).
move /(_ ltac:(done)) => [A [?]].
rewrite - ? app_assoc => ?.
by exists A.
Admitted.

Theorem reduction : MPCPb ⪯ (HSC_PRV Argument.ΓPCP).
Proof.
exists (fun '((v, w), P) => (Argument.PCPf ((v, w) :: P) v w)).
intros [[v w] P].
constructor.
-
exact Argument.ΓPCP_soundness.
-
Admitted.

Lemma ΓPCP_completeness {v w P} : hsc ΓPCP (PCPf ((v, w) :: P) v w) -> MPCPb ((v, w), P).
Proof.
move /hsc_der => [n].
have -> : PCPf ((v, w) :: P) v w = PCPf' ((v, w) :: P) ((v, w) :: P) (encode_pair (encode_word' bullet v) (encode_list encode_bool [])) (encode_pair (encode_word' bullet w) (encode_list encode_bool [])) by done.
move /ΓPCP_completeness_ind.
by apply.

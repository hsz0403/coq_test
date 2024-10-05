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
Admitted.

Lemma encode_word_app {v x} : encode_word (v ++ x) = append_word (encode_word v) x.
Proof.
elim: x v.
{
move=> v.
by rewrite app_nil_r.
}
move=> a x IH v.
rewrite -/(app [a] _) ? app_assoc IH encode_word_last /=.
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
case: a.
-
apply: IH.
rewrite encode_word_last.
move=> /=.
by congruence.
-
apply: IH.
rewrite encode_word_last.
move=> /=.
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

Lemma transparent_encode_pair {ζ s t} : ζ 0 = var 0 -> substitute ζ (encode_pair s t) = encode_pair (substitute ζ s) (substitute ζ t).
Proof.
Admitted.

Lemma transparent_append_word {ζ s v} : ζ 0 = var 0 -> substitute ζ (append_word s v) = append_word (substitute ζ s) v.
Proof.
move=> Hζ.
elim: v s; first done.
move=> a v IH s /=.
Admitted.

Lemma substitute_arrP {ζ s t} : substitute ζ (arr s t) = arr (substitute ζ s) (substitute ζ t).
Proof.
Admitted.

Lemma not_ΓPCP_rrr n r : not (der ΓPCP n (arr r (arr r r))).
Proof.
elim: n r; first by move=> ? /der_0E.
move=> n IH r /derE => [[ζ [s [k [_ [+ [+]]]]]]].
rewrite /ΓPCP /In -/ΓPCP.
case; last case; last case; last case; last case; last done.
all: move=> <-.
{
case: k => [|k] /=; last by move=> /ForallE [/IH].
move=> _ [<- _] /(f_equal size) => /=.
by lia.
}
all: case: k => [|k] /=.
1,3,5,7: by (move=> _; case=> _ <-; move /(f_equal size) => /=; by lia).
all: case: k => [|k] /=.
1,3,5,7: by (move=> _; case=> <- _; move /(f_equal size) => /=; by lia).
Admitted.

Lemma encode_word'_last {x a} : encode_word' bullet (x ++ [a]) = encode_pair (encode_word' bullet x) (encode_bool a).
Proof.
move: (bullet) => s.
elim: x s; first done.
Admitted.

Lemma hscI {Gamma ζ s t} : In s Gamma -> t = substitute ζ s -> hsc Gamma t.
Proof.
Admitted.

Lemma ΓPCP_assoc_x {P x r v} : hsc ΓPCP (PCPf' P P (encode_pair (encode_word' bullet (x ++ v)) bullet) r) -> hsc ΓPCP (PCPf' P P (encode_pair (encode_word' bullet x) (encode_list encode_bool v)) r).
Proof.
elim: v x.
{
move=> ?.
by rewrite app_nil_r.
}
move=> a v IH x.
rewrite -/(app [a] _) app_assoc.
move /IH.
rewrite encode_word'_last.
move /(hsc_arr _ _ _ _).
apply.
evar (ζ : nat -> formula).
instantiate (ζ := fun x => match x with | 0 => _ | 1 => _ | 2 => _ | 3 => _| 4 => _ | _ => _ end).
apply: (hscI (ζ := ζ)).
{
rewrite /ΓPCP.
do 3 right.
left.
by reflexivity.
}
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
by move /IH => ->.

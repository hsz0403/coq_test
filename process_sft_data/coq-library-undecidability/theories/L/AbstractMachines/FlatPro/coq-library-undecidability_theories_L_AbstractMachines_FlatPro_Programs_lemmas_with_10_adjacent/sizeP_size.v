From Undecidability.L Require Import Prelim.MoreBase Util.L_facts AbstractMachines.LargestVar.
Require Import Lia.
Require Export Undecidability.L.AbstractMachines.FlatPro.ProgramsDef.
Definition sizeT t := match t with varT n => 1 + n | _ => 1 end.
Definition sizeP (P:Pro) := sumn (map sizeT P) + 1.
Hint Unfold sizeP : core.
Fixpoint jumpTarget (l:nat) (res:Pro) (P:Pro) : option (Pro*Pro) := match P with | retT :: P => match l with | 0 => Some (res,P) | S l => jumpTarget l (res++[retT]) P end | lamT :: P => jumpTarget (S l) (res++[lamT])P | t :: P => jumpTarget l (res++[t]) P | [] => None end.
Fixpoint substP (P:Pro) k Q : Pro := match P with [] => [] | lamT::P => lamT::substP P (S k) Q | retT::P => retT::match k with S k => substP P k Q | 0 => [(* doesnt matter *)] end | varT k'::P => (if k' =? k then Q else [varT k'])++substP P k Q | appT::P => appT::substP P k Q end.
Fixpoint decompile l P A {struct P}: (list term) + (nat * Pro * list term) := match P with retT::P => match l with 0 => inr (l,retT::P,A) | S l => match A with s::A => decompile l P (lam s::A) | [] => inr (S l, retT::P, A) end end | varT n::P => decompile l P (var n::A) | lamT::P => decompile (S l) P A | appT::P => match A with t::s::A => decompile l P (app s t::A) | _ => inr (l, appT::P, A) end | [] => inl A end.
Definition Tok_eqb (t t' : Tok) := match t,t' with varT n, varT n' => Nat.eqb n n' | retT,retT => true | lamT, lamT => true | appT, appT => true | _,_ => false end.
Definition largestVarT t := match t with varT n => n | _ => 0 end.
Definition largestVarP P := maxl (map largestVarT P).

Lemma size_geq_1 s: 1<= size s.
Proof.
induction s;cbn.
Admitted.

Lemma sizeP_size' s :size s <= sumn (map sizeT (compile s)).
Proof.
induction s;cbn.
all:autorewrite with list.
all:cbn.
Admitted.

Lemma le_length_sizeP P : length P <= sizeP P.
Proof.
unfold sizeP.
Admitted.

Lemma length_compile_leq s : |compile s| <= 2*size s.
Proof.
induction s;cbn.
all:autorewrite with list;cbn.
Admitted.

Lemma jumpTarget_correct s c: jumpTarget 0 [] (compile s ++ retT::c) = Some (compile s,c).
Proof.
change (Some (compile s,c)) with (jumpTarget 0 ([]++compile s) (retT::c)).
generalize 0.
generalize (retT::c) as c'.
clear c.
generalize (@nil Tok) as c.
induction s;intros c' c l.
-
reflexivity.
-
cbn.
autorewrite with list.
rewrite IHs1,IHs2.
cbn.
now autorewrite with list.
-
cbn.
autorewrite with list.
rewrite IHs.
cbn.
Admitted.

Lemma substP_correct' s k c' t: substP (compile s++c') k (compile t) = compile (subst s k t)++substP c' k (compile t).
Proof.
induction s in k,c'|-*;cbn.
-
destruct (Nat.eqb_spec n k);cbn.
all:now autorewrite with list.
-
autorewrite with list.
rewrite IHs1,IHs2.
reflexivity.
-
autorewrite with list.
rewrite IHs.
Admitted.

Lemma substP_correct s k t: substP (compile s) k (compile t) = compile (subst s k t).
Proof.
replace (compile s) with (compile s++[]) by now autorewrite with list.
rewrite substP_correct'.
Admitted.

Lemma decompile_correct' l s P A: decompile l (compile s++P) A = decompile l P (s::A).
Proof.
induction s in l,P,A|-*.
all:cbn.
-
congruence.
-
autorewrite with list.
rewrite IHs1.
cbn.
rewrite IHs2.
reflexivity.
-
autorewrite with list.
rewrite IHs.
Admitted.

Lemma decompile_correct l s: decompile l (compile s) [] = inl [s].
Proof.
specialize (decompile_correct' l s [] []) as H.
autorewrite with list in H.
rewrite H.
Admitted.

Lemma decompile_resSize l P A B: decompile l P A = inl B -> sumn (map size B) <= sumn (map size A) + sumn (map sizeT P).
Proof.
induction P as [ |[] P] in l,A|-*.
-
cbn.
intros [= ->].
nia.
-
cbn.
intros ->%IHP.
cbn.
nia.
-
destruct A as [ | ? []].
1,2:easy.
intros ->%IHP.
cbn.
nia.
-
cbn.
intros ->%IHP.
nia.
-
destruct l.
easy.
destruct A as [].
1:easy.
intros ->%IHP.
cbn.
nia.
Admitted.

Lemma compile_inj s s' : compile s = compile s' -> s = s'.
Proof.
intros eq.
specialize (@decompile_correct' 0 s [] []) as H1.
specialize (@decompile_correct' 0 s' [] []) as H2.
rewrite eq in H1.
rewrite H1 in H2.
Admitted.

Lemma compile_neq_nil s: compile s <> [].
Proof.
edestruct (compile s) eqn:eq.
2:easy.
specialize decompile_correct' with (l:=0) (s:=s) (P:=[]) (A:=[]).
rewrite eq.
cbn.
Admitted.

Lemma sizeP_size s: sumn (map sizeT (compile s)) + 1<= 2*size s.
Proof.
induction s;cbn.
all:autorewrite with list.
all:cbn.
all:try lia.

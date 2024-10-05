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

Lemma compile_neq_nil s: compile s <> [].
Proof.
edestruct (compile s) eqn:eq.
2:easy.
specialize decompile_correct' with (l:=0) (s:=s) (P:=[]) (A:=[]).
rewrite eq.
cbn.
easy.

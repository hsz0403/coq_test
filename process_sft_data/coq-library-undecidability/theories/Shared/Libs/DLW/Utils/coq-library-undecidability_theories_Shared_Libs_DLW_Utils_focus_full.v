Require Import List.
Ltac lrev l := let rec loop aa ll := match ll with | ?x::?ll => loop (x::aa) ll | nil => constr:(aa) end in match type of l with | list ?t => loop (@nil t) l end.
Ltac lflat l := let rec loop aa ll := match ll with | ?ss++?rr => let bb := loop aa ss in let cc := loop bb rr in constr:(cc) | ?x::?rr => let bb := loop ((x::nil)::aa) rr in constr:(bb) | nil => constr:(aa) | ?ss => constr:(ss::aa) end in match type of l with | list ?t => let r1 := loop (@nil (list t)) l in lrev r1 end.
Ltac llin l := let rec loop aa ll := match ll with | (?x::nil)::?ll => let bb := loop (x::aa) ll in constr:(bb) | ?lx::?ll => let bb := loop (lx++aa) ll in constr:(bb) | nil => constr:(aa) end in match type of l with | list (list ?t) => match lrev l with | ?lx::?rr => let bb := loop lx rr in constr:(bb) | nil => constr:(@nil t) end end.
Ltac lcut x l := let rec loop aa x ll := match ll with | x::_ => let bb := lrev aa in constr:(bb++ll) | ?lz::?rr => let bb := loop (lz::aa) x rr in constr:(bb) end in match type of l with | list (list ?t) => loop (@nil (list t)) x l end.
Ltac lmerge l := match l with | ?aa++?ll => let bb := llin aa in let cc := llin ll in constr:(bb++cc) end.
Ltac focus_lst z r0 := let r1 := lflat r0 in let r2 := lcut z r1 in let r3 := lmerge r2 in constr:(r3).
Ltac focus_lst_2 z r0 := let r1 := focus_lst z r0 in let r2 := match r1 with | ?l++?x::?r => let r3 := focus_lst z r in match r3 with | ?m++?y::?n => constr:((l++x::m)++y::n) end end in constr:(r2).
Ltac focus_lst_3 z r0 := let r1 := focus_lst_2 z r0 in let r2 := match r1 with | ?l++?x::?r => let r3 := focus_lst z r in match r3 with | ?m++?y::?n => constr:((l++x::m)++y::n) end end in constr:(r2).
Ltac focus_elt z l := focus_lst (z::nil) l.
Section test.
Variable X : Type.
Variable x y z : list X.
Variable a b c : X.
End test.
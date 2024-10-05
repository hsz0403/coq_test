From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LNat LTerm LBool LProd List.List_enc LOptions.
Instance term_nat_enc : computableTime' (nat_enc) (fun n _ => (n * 14 + 12,tt)).
Proof.
extract.
solverec.
Instance term_term_enc : computableTime' (term_enc) (fun s _ => (size s * 30,tt)).
Proof.
extract.
solverec.
Instance bool_enc :computableTime' (@bool_enc) (fun l _ => (12,tt)).
Proof.
unfold bool_enc.
extract.
solverec.
Instance term_prod_enc X Y (R1:registered X) (R2:registered Y) t__X t__Y `{computableTime' (@enc X _) t__X} `{computableTime' (@enc Y _) t__Y} :computableTime' (@prod_enc X Y R1 R2) (fun w _ => (let '(x,y):= w in fst (t__X x tt) + fst (t__Y y tt) + 15,tt)).
Proof.
unfold prod_enc.
change (match R1 with | @mk_registered _ enc _ _ => enc end) with (enc (registered:=R1)).
change (match R2 with | @mk_registered _ enc _ _ => enc end) with (enc (registered:=R2)).
extract.
solverec.
Instance term_list_enc X (R:registered X) t__X `{computableTime' (@enc X _) t__X} :computableTime' (@list_enc X R) (fun l _ => (sumn (map (fun x => fst (t__X x tt) + 17) l) + 12,tt)).
Proof.
unfold list_enc.
change (match R with | @mk_registered _ enc _ _ => enc end) with (enc (registered:=R)).
extract.
solverec.
Import LOptions.
Instance term_option_enc X (R:registered X) t__X `{computableTime' (@enc X _) t__X} :computableTime' (@option_enc X R) (fun x _ => (match x with Some x => fst (t__X x tt) | _ => 0 end + 15,tt)).
Proof.
unfold option_enc.
change (match R with | @mk_registered _ enc _ _ => enc end) with (enc (registered:=R)).
extract.
solverec.

Instance bool_enc :computableTime' (@bool_enc) (fun l _ => (12,tt)).
Proof.
unfold bool_enc.
extract.
solverec.

Require Export Replace2.
Require Import NAux ZAux RAux.
Require P.
Definition Natopp := (fun x:nat => 0%nat).
Definition Nopp := (fun x:N => 0%N).
Definition is_Z0 := Zeq_bool 0.
Definition is_Z1 := Zeq_bool 1.
Definition is_Zpos := Zle_bool 0.
Definition is_Zdiv x y := if Zeq_bool x Z0 then false else Zeq_bool Z0 (Zmod y x).
Definition Zgcd x y := if is_Zdiv x y then x else if is_Zdiv y x then y else 1%Z.
Ltac is_NatCst p := match p with | O => constr:(true) | S ?p' => is_NatCst p' | _ => constr:(false) end.
Ltac NatCst t := match is_NatCst t with | false => constr:(false) | _ => let res := eval compute in (Z_of_nat t) in constr:(res) end.
Ltac is_PCst p := match p with | xH => constr:(true) | xO ?p' => is_PCst p' | xI ?p' => is_PCst p' | _ => constr:(false) end.
Ltac is_NCst p := match p with | N0 => constr:(true) | Npos ?p' => is_PCst p' | _ => constr:(false) end.
Ltac NCst t := match is_NCst t with | false => constr:(false) | _ => let res := eval compute in (Z_of_N t) in constr:(res) end.
Ltac ZCst t := match t with | Z0 => constr:(t) | Zpos ?p => match is_PCst p with | false => constr:(false) | _ => constr:(t) end | Zneg ?p => match is_PCst p with | false => constr:(false) | _ => constr:(t) end | _ => constr:(false) end.
Ltac is_ZCst t := match t with | Z0 => constr:(true) | Zpos ?p => is_PCst p | Zneg ?p => is_PCst p | _ => constr:(false) end.
Fixpoint P2R (z: positive) {struct z}: R := match z with | xH => 1%R | xO xH => 2%R | xI xH => 3%R | xO z1 => (2 * P2R z1)%R | xI z1 => (1 + 2 * P2R z1)%R end.
Definition Z2R (z: Z): R := match z with | Z0 => 0%R | Zpos z1 => (P2R z1)%R | Zneg z1 => (-(P2R z1))%R end.
Ltac RCst t := match t with | R0 => constr:(Z0) | R1 => constr:(Zpos xH) | Rplus ?e1 ?e2 => match (RCst e1) with | false => constr:(false) | ?e3 => match (RCst e2) with | false => constr:(false) | ?e4 => eval vm_compute in (Zplus e3 e4) end end | Rminus ?e1 ?e2 => match (RCst e1) with | false => constr:(false) | ?e3 => match (RCst e2) with | false => constr:(false) | ?e4 => eval vm_compute in (Zminus e3 e4) end end | Rmult ?e1 ?e2 => match (RCst e1) with | false => constr:(false) | ?e3 => match (RCst e2) with | false => constr:(false) | ?e4 => eval vm_compute in (Zmult e3 e4) end end | Ropp ?e1 => match (RCst e1) with | false => constr:(false) | ?e3 => eval vm_compute in (Z.opp e3) end | IZR ?e1 => match (ZCst e1) with | false => constr:(false) | ?e3 => e3 end | _ => constr:(false) end.
Ltac clean_zabs term := match term with | context id [(Z.abs_nat ?X)] => match is_ZCst X with | true => let x := (eval vm_compute in (Z.abs_nat X)) in let y := context id [x] in clean_zabs y | false => term end | _ => term end.
Ltac clean_zabs_N term := match term with | context id [(Z.abs_N ?X)] => match is_ZCst X with | true => let x := (eval vm_compute in (Z.abs_N X)) in let y := context id [x] in clean_zabs_N y | false => term end | _ => term end.
Ltac eqterm t1 t2 := match constr:((t1,t2)) with (?X, ?X) => true | _ => false end.
Open Scope nat_scope.
Close Scope nat_scope.
Open Scope N_scope.
Close Scope N_scope.
Open Scope Z_scope.
Close Scope Z_scope.
Open Scope R_scope.
Close Scope R_scope.

Theorem Nplus_eq_compat_l: forall a b c, b = c -> a + b = a + c.
Proof.
intros; apply f_equal2 with (f:= Nplus); auto.

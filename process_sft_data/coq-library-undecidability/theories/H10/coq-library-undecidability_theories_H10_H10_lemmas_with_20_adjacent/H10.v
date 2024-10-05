From Undecidability.Shared.Libs.DLW Require Import pos vec.
From Undecidability.H10.Dio Require Import dio_single.
Set Implicit Arguments.
Definition H10_PROBLEM := { n : nat & dio_polynomial (pos n) (pos 0) * dio_polynomial (pos n) (pos 0) }%type.
Definition H10 : H10_PROBLEM -> Prop.
Proof.
intros (n & p & q).
apply (dio_single_pred (p,q)), (fun _ => 0).
Defined.

Definition H10 : H10_PROBLEM -> Prop.
Proof.
intros (n & p & q).
apply (dio_single_pred (p,q)), (fun _ => 0).

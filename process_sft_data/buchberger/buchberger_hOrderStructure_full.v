Variable n : nat.
Variable ltM : mon n -> mon n -> Prop.
Variable ltM_dec : forall a b : mon n, {ltM a b} + {ltM b a} + {a = b}.
Variable os : OrderStructure (mon n) (zero_mon n) ltM (mult_mon n).
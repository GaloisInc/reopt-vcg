def notb1 : instruction :=
  definst "notb" $ do
    pattern fun (v_2957 : reg (bv 8)) => do
      v_4551 <- getRegister v_2957;
      setRegister (lhs.of_reg v_2957) (bv_xor v_4551 (expression.bv_nat 8 255));
      pure ()
    pat_end;
    pattern fun (v_2950 : Mem) => do
      v_10812 <- evaluateAddress v_2950;
      v_10813 <- load v_10812 1;
      store v_10812 (bv_xor v_10813 (expression.bv_nat 8 255)) 1;
      pure ()
    pat_end

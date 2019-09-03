def notw1 : instruction :=
  definst "notw" $ do
    pattern fun (v_2902 : reg (bv 16)) => do
      v_4627 <- getRegister v_2902;
      setRegister (lhs.of_reg v_2902) (bv_xor v_4627 (expression.bv_nat 16 65535));
      pure ()
    pat_end;
    pattern fun (v_2899 : Mem) => do
      v_11110 <- evaluateAddress v_2899;
      v_11111 <- load v_11110 2;
      store v_11110 (bv_xor v_11111 (expression.bv_nat 16 65535)) 2;
      pure ()
    pat_end

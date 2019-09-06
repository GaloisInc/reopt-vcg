def notw1 : instruction :=
  definst "notw" $ do
    pattern fun (v_2978 : reg (bv 16)) => do
      v_4569 <- getRegister v_2978;
      setRegister (lhs.of_reg v_2978) (bv_xor v_4569 (expression.bv_nat 16 65535));
      pure ()
    pat_end;
    pattern fun (v_2975 : Mem) => do
      v_10824 <- evaluateAddress v_2975;
      v_10825 <- load v_10824 2;
      store v_10824 (bv_xor v_10825 (expression.bv_nat 16 65535)) 2;
      pure ()
    pat_end

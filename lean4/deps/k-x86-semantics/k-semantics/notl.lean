def notl1 : instruction :=
  definst "notl" $ do
    pattern fun (v_2888 : reg (bv 32)) => do
      v_4615 <- getRegister v_2888;
      setRegister (lhs.of_reg v_2888) (bv_xor v_4615 (expression.bv_nat 32 4294967295));
      pure ()
    pat_end;
    pattern fun (v_2885 : Mem) => do
      v_11102 <- evaluateAddress v_2885;
      v_11103 <- load v_11102 4;
      store v_11102 (bv_xor v_11103 (expression.bv_nat 32 4294967295)) 4;
      pure ()
    pat_end

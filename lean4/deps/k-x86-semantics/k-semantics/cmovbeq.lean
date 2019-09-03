def cmovbeq1 : instruction :=
  definst "cmovbeq" $ do
    pattern fun (v_2465 : reg (bv 64)) (v_2466 : reg (bv 64)) => do
      v_4140 <- getRegister cf;
      v_4142 <- getRegister zf;
      v_4145 <- getRegister v_2465;
      v_4146 <- getRegister v_2466;
      setRegister (lhs.of_reg v_2466) (mux (bit_or (eq v_4140 (expression.bv_nat 1 1)) (eq v_4142 (expression.bv_nat 1 1))) v_4145 v_4146);
      pure ()
    pat_end;
    pattern fun (v_2457 : Mem) (v_2458 : reg (bv 64)) => do
      v_7845 <- getRegister cf;
      v_7847 <- getRegister zf;
      v_7850 <- evaluateAddress v_2457;
      v_7851 <- load v_7850 8;
      v_7852 <- getRegister v_2458;
      setRegister (lhs.of_reg v_2458) (mux (bit_or (eq v_7845 (expression.bv_nat 1 1)) (eq v_7847 (expression.bv_nat 1 1))) v_7851 v_7852);
      pure ()
    pat_end

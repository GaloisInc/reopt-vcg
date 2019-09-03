def cmovnal1 : instruction :=
  definst "cmovnal" $ do
    pattern fun (v_2755 : reg (bv 32)) (v_2756 : reg (bv 32)) => do
      v_4504 <- getRegister cf;
      v_4506 <- getRegister zf;
      v_4509 <- getRegister v_2755;
      v_4510 <- getRegister v_2756;
      setRegister (lhs.of_reg v_2756) (mux (bit_or (eq v_4504 (expression.bv_nat 1 1)) (eq v_4506 (expression.bv_nat 1 1))) v_4509 v_4510);
      pure ()
    pat_end;
    pattern fun (v_2751 : Mem) (v_2752 : reg (bv 32)) => do
      v_8103 <- getRegister cf;
      v_8105 <- getRegister zf;
      v_8108 <- evaluateAddress v_2751;
      v_8109 <- load v_8108 4;
      v_8110 <- getRegister v_2752;
      setRegister (lhs.of_reg v_2752) (mux (bit_or (eq v_8103 (expression.bv_nat 1 1)) (eq v_8105 (expression.bv_nat 1 1))) v_8109 v_8110);
      pure ()
    pat_end

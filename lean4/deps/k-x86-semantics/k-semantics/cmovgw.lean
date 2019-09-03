def cmovgw1 : instruction :=
  definst "cmovgw" $ do
    pattern fun (v_2629 : reg (bv 16)) (v_2630 : reg (bv 16)) => do
      v_4336 <- getRegister zf;
      v_4339 <- getRegister sf;
      v_4341 <- getRegister of;
      v_4345 <- getRegister v_2629;
      v_4346 <- getRegister v_2630;
      setRegister (lhs.of_reg v_2630) (mux (bit_and (notBool_ (eq v_4336 (expression.bv_nat 1 1))) (eq (eq v_4339 (expression.bv_nat 1 1)) (eq v_4341 (expression.bv_nat 1 1)))) v_4345 v_4346);
      pure ()
    pat_end;
    pattern fun (v_2626 : Mem) (v_2625 : reg (bv 16)) => do
      v_8017 <- getRegister zf;
      v_8020 <- getRegister sf;
      v_8022 <- getRegister of;
      v_8026 <- evaluateAddress v_2626;
      v_8027 <- load v_8026 2;
      v_8028 <- getRegister v_2625;
      setRegister (lhs.of_reg v_2625) (mux (bit_and (notBool_ (eq v_8017 (expression.bv_nat 1 1))) (eq (eq v_8020 (expression.bv_nat 1 1)) (eq v_8022 (expression.bv_nat 1 1)))) v_8027 v_8028);
      pure ()
    pat_end

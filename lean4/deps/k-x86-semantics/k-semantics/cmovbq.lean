def cmovbq1 : instruction :=
  definst "cmovbq" $ do
    pattern fun (v_2489 : reg (bv 64)) (v_2490 : reg (bv 64)) => do
      v_4168 <- getRegister cf;
      v_4170 <- getRegister v_2489;
      v_4171 <- getRegister v_2490;
      setRegister (lhs.of_reg v_2490) (mux (eq v_4168 (expression.bv_nat 1 1)) v_4170 v_4171);
      pure ()
    pat_end;
    pattern fun (v_2484 : Mem) (v_2485 : reg (bv 64)) => do
      v_7900 <- getRegister cf;
      v_7902 <- evaluateAddress v_2484;
      v_7903 <- load v_7902 8;
      v_7904 <- getRegister v_2485;
      setRegister (lhs.of_reg v_2485) (mux (eq v_7900 (expression.bv_nat 1 1)) v_7903 v_7904);
      pure ()
    pat_end

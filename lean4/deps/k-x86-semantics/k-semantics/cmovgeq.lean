def cmovgeq1 : instruction :=
  definst "cmovgeq" $ do
    pattern fun (v_2586 : reg (bv 64)) (v_2587 : reg (bv 64)) => do
      v_4271 <- getRegister sf;
      v_4273 <- getRegister of;
      v_4276 <- getRegister v_2586;
      v_4277 <- getRegister v_2587;
      setRegister (lhs.of_reg v_2587) (mux (eq (eq v_4271 (expression.bv_nat 1 1)) (eq v_4273 (expression.bv_nat 1 1))) v_4276 v_4277);
      pure ()
    pat_end;
    pattern fun (v_2577 : Mem) (v_2578 : reg (bv 64)) => do
      v_7968 <- getRegister sf;
      v_7970 <- getRegister of;
      v_7973 <- evaluateAddress v_2577;
      v_7974 <- load v_7973 8;
      v_7975 <- getRegister v_2578;
      setRegister (lhs.of_reg v_2578) (mux (eq (eq v_7968 (expression.bv_nat 1 1)) (eq v_7970 (expression.bv_nat 1 1))) v_7974 v_7975);
      pure ()
    pat_end

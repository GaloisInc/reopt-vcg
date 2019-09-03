def cmovgel1 : instruction :=
  definst "cmovgel" $ do
    pattern fun (v_2580 : reg (bv 32)) (v_2581 : reg (bv 32)) => do
      v_4266 <- getRegister sf;
      v_4268 <- getRegister of;
      v_4271 <- getRegister v_2580;
      v_4272 <- getRegister v_2581;
      setRegister (lhs.of_reg v_2581) (mux (eq (eq v_4266 (expression.bv_nat 1 1)) (eq v_4268 (expression.bv_nat 1 1))) v_4271 v_4272);
      pure ()
    pat_end;
    pattern fun (v_2572 : Mem) (v_2573 : reg (bv 32)) => do
      v_7930 <- getRegister sf;
      v_7932 <- getRegister of;
      v_7935 <- evaluateAddress v_2572;
      v_7936 <- load v_7935 4;
      v_7937 <- getRegister v_2573;
      setRegister (lhs.of_reg v_2573) (mux (eq (eq v_7930 (expression.bv_nat 1 1)) (eq v_7932 (expression.bv_nat 1 1))) v_7936 v_7937);
      pure ()
    pat_end

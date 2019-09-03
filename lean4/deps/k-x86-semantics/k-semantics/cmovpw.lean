def cmovpw1 : instruction :=
  definst "cmovpw" $ do
    pattern fun (v_3231 : reg (bv 16)) (v_3232 : reg (bv 16)) => do
      v_5130 <- getRegister pf;
      v_5132 <- getRegister v_3231;
      v_5133 <- getRegister v_3232;
      setRegister (lhs.of_reg v_3232) (mux (eq v_5130 (expression.bv_nat 1 1)) v_5132 v_5133);
      pure ()
    pat_end;
    pattern fun (v_3225 : Mem) (v_3227 : reg (bv 16)) => do
      v_8567 <- getRegister pf;
      v_8569 <- evaluateAddress v_3225;
      v_8570 <- load v_8569 2;
      v_8571 <- getRegister v_3227;
      setRegister (lhs.of_reg v_3227) (mux (eq v_8567 (expression.bv_nat 1 1)) v_8570 v_8571);
      pure ()
    pat_end

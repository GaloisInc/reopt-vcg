def cmovpeq1 : instruction :=
  definst "cmovpeq" $ do
    pattern fun (v_3218 : reg (bv 64)) (v_3219 : reg (bv 64)) => do
      v_5108 <- getRegister pf;
      v_5110 <- getRegister v_3218;
      v_5111 <- getRegister v_3219;
      setRegister (lhs.of_reg v_3219) (mux (eq v_5108 (expression.bv_nat 1 1)) v_5110 v_5111);
      pure ()
    pat_end;
    pattern fun (v_3213 : Mem) (v_3214 : reg (bv 64)) => do
      v_8528 <- getRegister pf;
      v_8530 <- evaluateAddress v_3213;
      v_8531 <- load v_8530 8;
      v_8532 <- getRegister v_3214;
      setRegister (lhs.of_reg v_3214) (mux (eq v_8528 (expression.bv_nat 1 1)) v_8531 v_8532);
      pure ()
    pat_end

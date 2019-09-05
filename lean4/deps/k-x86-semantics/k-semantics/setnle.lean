def setnle1 : instruction :=
  definst "setnle" $ do
    pattern fun (v_2660 : reg (bv 8)) => do
      v_4225 <- getRegister zf;
      v_4228 <- getRegister sf;
      v_4230 <- getRegister of;
      setRegister (lhs.of_reg v_2660) (mux (bit_and (notBool_ (eq v_4225 (expression.bv_nat 1 1))) (eq (eq v_4228 (expression.bv_nat 1 1)) (eq v_4230 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2652 : Mem) => do
      v_8600 <- evaluateAddress v_2652;
      v_8601 <- getRegister zf;
      v_8604 <- getRegister sf;
      v_8606 <- getRegister of;
      store v_8600 (mux (bit_and (notBool_ (eq v_8601 (expression.bv_nat 1 1))) (eq (eq v_8604 (expression.bv_nat 1 1)) (eq v_8606 (expression.bv_nat 1 1)))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

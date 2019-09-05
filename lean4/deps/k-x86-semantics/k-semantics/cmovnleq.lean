def cmovnleq1 : instruction :=
  definst "cmovnleq" $ do
    pattern fun (v_3005 : reg (bv 64)) (v_3006 : reg (bv 64)) => do
      v_4848 <- getRegister zf;
      v_4851 <- getRegister sf;
      v_4853 <- getRegister of;
      v_4857 <- getRegister v_3005;
      v_4858 <- getRegister v_3006;
      setRegister (lhs.of_reg v_3006) (mux (bit_and (notBool_ (eq v_4848 (expression.bv_nat 1 1))) (eq (eq v_4851 (expression.bv_nat 1 1)) (eq v_4853 (expression.bv_nat 1 1)))) v_4857 v_4858);
      pure ()
    pat_end;
    pattern fun (v_3000 : Mem) (v_3001 : reg (bv 64)) => do
      v_8343 <- getRegister zf;
      v_8346 <- getRegister sf;
      v_8348 <- getRegister of;
      v_8352 <- evaluateAddress v_3000;
      v_8353 <- load v_8352 8;
      v_8354 <- getRegister v_3001;
      setRegister (lhs.of_reg v_3001) (mux (bit_and (notBool_ (eq v_8343 (expression.bv_nat 1 1))) (eq (eq v_8346 (expression.bv_nat 1 1)) (eq v_8348 (expression.bv_nat 1 1)))) v_8353 v_8354);
      pure ()
    pat_end

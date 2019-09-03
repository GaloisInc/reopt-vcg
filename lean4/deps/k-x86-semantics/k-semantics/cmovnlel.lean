def cmovnlel1 : instruction :=
  definst "cmovnlel" $ do
    pattern fun (v_2932 : reg (bv 32)) (v_2933 : reg (bv 32)) => do
      v_4767 <- getRegister zf;
      v_4770 <- getRegister sf;
      v_4772 <- getRegister of;
      v_4776 <- getRegister v_2932;
      v_4777 <- getRegister v_2933;
      setRegister (lhs.of_reg v_2933) (mux (bit_and (notBool_ (eq v_4767 (expression.bv_nat 1 1))) (eq (eq v_4770 (expression.bv_nat 1 1)) (eq v_4772 (expression.bv_nat 1 1)))) v_4776 v_4777);
      pure ()
    pat_end;
    pattern fun (v_2928 : Mem) (v_2929 : reg (bv 32)) => do
      v_8343 <- getRegister zf;
      v_8346 <- getRegister sf;
      v_8348 <- getRegister of;
      v_8352 <- evaluateAddress v_2928;
      v_8353 <- load v_8352 4;
      v_8354 <- getRegister v_2929;
      setRegister (lhs.of_reg v_2929) (mux (bit_and (notBool_ (eq v_8343 (expression.bv_nat 1 1))) (eq (eq v_8346 (expression.bv_nat 1 1)) (eq v_8348 (expression.bv_nat 1 1)))) v_8353 v_8354);
      pure ()
    pat_end

def cmovgq1 : instruction :=
  definst "cmovgq" $ do
    pattern fun (v_2684 : reg (bv 64)) (v_2685 : reg (bv 64)) => do
      v_4383 <- getRegister zf;
      v_4386 <- getRegister sf;
      v_4388 <- getRegister of;
      v_4392 <- getRegister v_2684;
      v_4393 <- getRegister v_2685;
      setRegister (lhs.of_reg v_2685) (mux (bit_and (notBool_ (eq v_4383 (expression.bv_nat 1 1))) (eq (eq v_4386 (expression.bv_nat 1 1)) (eq v_4388 (expression.bv_nat 1 1)))) v_4392 v_4393);
      pure ()
    pat_end;
    pattern fun (v_2679 : Mem) (v_2680 : reg (bv 64)) => do
      v_7989 <- getRegister zf;
      v_7992 <- getRegister sf;
      v_7994 <- getRegister of;
      v_7998 <- evaluateAddress v_2679;
      v_7999 <- load v_7998 8;
      v_8000 <- getRegister v_2680;
      setRegister (lhs.of_reg v_2680) (mux (bit_and (notBool_ (eq v_7989 (expression.bv_nat 1 1))) (eq (eq v_7992 (expression.bv_nat 1 1)) (eq v_7994 (expression.bv_nat 1 1)))) v_7999 v_8000);
      pure ()
    pat_end

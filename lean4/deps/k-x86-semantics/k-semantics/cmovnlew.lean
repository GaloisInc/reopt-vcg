def cmovnlew1 : instruction :=
  definst "cmovnlew" $ do
    pattern fun (v_2950 : reg (bv 16)) (v_2951 : reg (bv 16)) => do
      v_4801 <- getRegister zf;
      v_4804 <- getRegister sf;
      v_4806 <- getRegister of;
      v_4810 <- getRegister v_2950;
      v_4811 <- getRegister v_2951;
      setRegister (lhs.of_reg v_2951) (mux (bit_and (notBool_ (eq v_4801 (expression.bv_nat 1 1))) (eq (eq v_4804 (expression.bv_nat 1 1)) (eq v_4806 (expression.bv_nat 1 1)))) v_4810 v_4811);
      pure ()
    pat_end;
    pattern fun (v_2947 : Mem) (v_2946 : reg (bv 16)) => do
      v_8371 <- getRegister zf;
      v_8374 <- getRegister sf;
      v_8376 <- getRegister of;
      v_8380 <- evaluateAddress v_2947;
      v_8381 <- load v_8380 2;
      v_8382 <- getRegister v_2946;
      setRegister (lhs.of_reg v_2946) (mux (bit_and (notBool_ (eq v_8371 (expression.bv_nat 1 1))) (eq (eq v_8374 (expression.bv_nat 1 1)) (eq v_8376 (expression.bv_nat 1 1)))) v_8381 v_8382);
      pure ()
    pat_end

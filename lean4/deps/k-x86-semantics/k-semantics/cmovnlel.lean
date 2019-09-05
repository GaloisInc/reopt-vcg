def cmovnlel1 : instruction :=
  definst "cmovnlel" $ do
    pattern fun (v_2998 : reg (bv 32)) (v_2999 : reg (bv 32)) => do
      v_4831 <- getRegister zf;
      v_4834 <- getRegister sf;
      v_4836 <- getRegister of;
      v_4840 <- getRegister v_2998;
      v_4841 <- getRegister v_2999;
      setRegister (lhs.of_reg v_2999) (mux (bit_and (notBool_ (eq v_4831 (expression.bv_nat 1 1))) (eq (eq v_4834 (expression.bv_nat 1 1)) (eq v_4836 (expression.bv_nat 1 1)))) v_4840 v_4841);
      pure ()
    pat_end;
    pattern fun (v_2991 : Mem) (v_2994 : reg (bv 32)) => do
      v_8329 <- getRegister zf;
      v_8332 <- getRegister sf;
      v_8334 <- getRegister of;
      v_8338 <- evaluateAddress v_2991;
      v_8339 <- load v_8338 4;
      v_8340 <- getRegister v_2994;
      setRegister (lhs.of_reg v_2994) (mux (bit_and (notBool_ (eq v_8329 (expression.bv_nat 1 1))) (eq (eq v_8332 (expression.bv_nat 1 1)) (eq v_8334 (expression.bv_nat 1 1)))) v_8339 v_8340);
      pure ()
    pat_end

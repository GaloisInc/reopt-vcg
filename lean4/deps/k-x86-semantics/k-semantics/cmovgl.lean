def cmovgl1 : instruction :=
  definst "cmovgl" $ do
    pattern fun (v_2611 : reg (bv 32)) (v_2612 : reg (bv 32)) => do
      v_4302 <- getRegister zf;
      v_4305 <- getRegister sf;
      v_4307 <- getRegister of;
      v_4311 <- getRegister v_2611;
      v_4312 <- getRegister v_2612;
      setRegister (lhs.of_reg v_2612) (mux (bit_and (notBool_ (eq v_4302 (expression.bv_nat 1 1))) (eq (eq v_4305 (expression.bv_nat 1 1)) (eq v_4307 (expression.bv_nat 1 1)))) v_4311 v_4312);
      pure ()
    pat_end;
    pattern fun (v_2607 : Mem) (v_2608 : reg (bv 32)) => do
      v_7989 <- getRegister zf;
      v_7992 <- getRegister sf;
      v_7994 <- getRegister of;
      v_7998 <- evaluateAddress v_2607;
      v_7999 <- load v_7998 4;
      v_8000 <- getRegister v_2608;
      setRegister (lhs.of_reg v_2608) (mux (bit_and (notBool_ (eq v_7989 (expression.bv_nat 1 1))) (eq (eq v_7992 (expression.bv_nat 1 1)) (eq v_7994 (expression.bv_nat 1 1)))) v_7999 v_8000);
      pure ()
    pat_end

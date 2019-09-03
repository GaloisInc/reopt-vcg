def cmoval1 : instruction :=
  definst "cmoval" $ do
    pattern fun (v_2413 : reg (bv 32)) (v_2414 : reg (bv 32)) => do
      v_4072 <- getRegister cf;
      v_4075 <- getRegister zf;
      v_4079 <- getRegister v_2413;
      v_4080 <- getRegister v_2414;
      setRegister (lhs.of_reg v_2414) (mux (bit_and (notBool_ (eq v_4072 (expression.bv_nat 1 1))) (notBool_ (eq v_4075 (expression.bv_nat 1 1)))) v_4079 v_4080);
      pure ()
    pat_end;
    pattern fun (v_2409 : Mem) (v_2410 : reg (bv 32)) => do
      v_7797 <- getRegister cf;
      v_7800 <- getRegister zf;
      v_7804 <- evaluateAddress v_2409;
      v_7805 <- load v_7804 4;
      v_7806 <- getRegister v_2410;
      setRegister (lhs.of_reg v_2410) (mux (bit_and (notBool_ (eq v_7797 (expression.bv_nat 1 1))) (notBool_ (eq v_7800 (expression.bv_nat 1 1)))) v_7805 v_7806);
      pure ()
    pat_end

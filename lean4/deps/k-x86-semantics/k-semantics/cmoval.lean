def cmoval1 : instruction :=
  definst "cmoval" $ do
    pattern fun (v_2401 : reg (bv 32)) (v_2402 : reg (bv 32)) => do
      v_4059 <- getRegister cf;
      v_4062 <- getRegister zf;
      v_4066 <- getRegister v_2401;
      v_4067 <- getRegister v_2402;
      setRegister (lhs.of_reg v_2402) (mux (bit_and (notBool_ (eq v_4059 (expression.bv_nat 1 1))) (notBool_ (eq v_4062 (expression.bv_nat 1 1)))) v_4066 v_4067);
      pure ()
    pat_end;
    pattern fun (v_2397 : Mem) (v_2398 : reg (bv 32)) => do
      v_7824 <- getRegister cf;
      v_7827 <- getRegister zf;
      v_7831 <- evaluateAddress v_2397;
      v_7832 <- load v_7831 4;
      v_7833 <- getRegister v_2398;
      setRegister (lhs.of_reg v_2398) (mux (bit_and (notBool_ (eq v_7824 (expression.bv_nat 1 1))) (notBool_ (eq v_7827 (expression.bv_nat 1 1)))) v_7832 v_7833);
      pure ()
    pat_end

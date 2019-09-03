def cmovaew1 : instruction :=
  definst "cmovaew" $ do
    pattern fun (v_2406 : reg (bv 16)) (v_2407 : reg (bv 16)) => do
      v_4061 <- getRegister cf;
      v_4064 <- getRegister v_2406;
      v_4065 <- getRegister v_2407;
      setRegister (lhs.of_reg v_2407) (mux (notBool_ (eq v_4061 (expression.bv_nat 1 1))) v_4064 v_4065);
      pure ()
    pat_end;
    pattern fun (v_2400 : Mem) (v_2402 : reg (bv 16)) => do
      v_7789 <- getRegister cf;
      v_7792 <- evaluateAddress v_2400;
      v_7793 <- load v_7792 2;
      v_7794 <- getRegister v_2402;
      setRegister (lhs.of_reg v_2402) (mux (notBool_ (eq v_7789 (expression.bv_nat 1 1))) v_7793 v_7794);
      pure ()
    pat_end

def cmovaew1 : instruction :=
  definst "cmovaew" $ do
    pattern fun (v_2392 : reg (bv 16)) (v_2393 : reg (bv 16)) => do
      v_4048 <- getRegister cf;
      v_4051 <- getRegister v_2392;
      v_4052 <- getRegister v_2393;
      setRegister (lhs.of_reg v_2393) (mux (notBool_ (eq v_4048 (expression.bv_nat 1 1))) v_4051 v_4052);
      pure ()
    pat_end;
    pattern fun (v_2389 : Mem) (v_2388 : reg (bv 16)) => do
      v_7816 <- getRegister cf;
      v_7819 <- evaluateAddress v_2389;
      v_7820 <- load v_7819 2;
      v_7821 <- getRegister v_2388;
      setRegister (lhs.of_reg v_2388) (mux (notBool_ (eq v_7816 (expression.bv_nat 1 1))) v_7820 v_7821);
      pure ()
    pat_end

def setae1 : instruction :=
  definst "setae" $ do
    pattern fun (v_2489 : reg (bv 8)) => do
      v_3943 <- getRegister cf;
      setRegister (lhs.of_reg v_2489) (mux (notBool_ v_3943) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2482 : Mem) => do
      v_7897 <- evaluateAddress v_2482;
      v_7898 <- getRegister cf;
      store v_7897 (mux (notBool_ v_7898) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

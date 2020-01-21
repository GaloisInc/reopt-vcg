def seta : instruction :=
  definst "seta" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- getRegister cf;
      v_3 <- getRegister zf;
      store v_1 (mux (bit_and (notBool_ v_2) (notBool_ v_3)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister cf;
      v_2 <- getRegister zf;
      setRegister (lhs.of_reg rh_0) (mux (bit_and (notBool_ v_1) (notBool_ v_2)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end

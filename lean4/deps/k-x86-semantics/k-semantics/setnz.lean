def setnz1 : instruction :=
  definst "setnz" $ do
    pattern fun (v_2731 : reg (bv 8)) => do
      v_4231 <- getRegister zf;
      setRegister (lhs.of_reg v_2731) (mux (notBool_ v_4231) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2724 : Mem) => do
      v_8030 <- evaluateAddress v_2724;
      v_8031 <- getRegister zf;
      store v_8030 (mux (notBool_ v_8031) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

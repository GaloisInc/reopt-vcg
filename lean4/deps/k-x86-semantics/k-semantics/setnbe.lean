def setnbe1 : instruction :=
  definst "setnbe" $ do
    pattern fun (v_2621 : reg (bv 8)) => do
      v_4096 <- getRegister cf;
      v_4098 <- getRegister zf;
      setRegister (lhs.of_reg v_2621) (mux (bit_and (notBool_ v_4096) (notBool_ v_4098)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2614 : Mem) => do
      v_7966 <- evaluateAddress v_2614;
      v_7967 <- getRegister cf;
      v_7969 <- getRegister zf;
      store v_7966 (mux (bit_and (notBool_ v_7967) (notBool_ v_7969)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

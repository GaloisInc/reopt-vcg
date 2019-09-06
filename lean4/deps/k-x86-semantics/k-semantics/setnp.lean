def setnp1 : instruction :=
  definst "setnp" $ do
    pattern fun (v_2709 : reg (bv 8)) => do
      v_4209 <- getRegister pf;
      setRegister (lhs.of_reg v_2709) (mux (notBool_ v_4209) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2702 : Mem) => do
      v_8020 <- evaluateAddress v_2702;
      v_8021 <- getRegister pf;
      store v_8020 (mux (notBool_ v_8021) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

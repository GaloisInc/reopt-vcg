def setne1 : instruction :=
  definst "setne" $ do
    pattern fun (v_2643 : reg (bv 8)) => do
      v_4121 <- getRegister zf;
      setRegister (lhs.of_reg v_2643) (mux (notBool_ v_4121) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2636 : Mem) => do
      v_7979 <- evaluateAddress v_2636;
      v_7980 <- getRegister zf;
      store v_7979 (mux (notBool_ v_7980) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

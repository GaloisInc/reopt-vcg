def setne1 : instruction :=
  definst "setne" $ do
    pattern fun (v_2616 : reg (bv 8)) => do
      v_4145 <- getRegister zf;
      setRegister (lhs.of_reg v_2616) (mux (notBool_ (eq v_4145 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2608 : Mem) => do
      v_8565 <- evaluateAddress v_2608;
      v_8566 <- getRegister zf;
      store v_8565 (mux (notBool_ (eq v_8566 (expression.bv_nat 1 1))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

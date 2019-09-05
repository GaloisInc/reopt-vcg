def setz1 : instruction :=
  definst "setz" $ do
    pattern fun (v_2770 : reg (bv 8)) => do
      v_4352 <- getRegister zf;
      setRegister (lhs.of_reg v_2770) (mux (eq v_4352 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2762 : Mem) => do
      v_8662 <- evaluateAddress v_2762;
      v_8663 <- getRegister zf;
      store v_8662 (mux (eq v_8663 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

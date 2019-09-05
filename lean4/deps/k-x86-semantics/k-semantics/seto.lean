def seto1 : instruction :=
  definst "seto" $ do
    pattern fun (v_2715 : reg (bv 8)) => do
      v_4295 <- getRegister of;
      setRegister (lhs.of_reg v_2715) (mux (eq v_4295 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2707 : Mem) => do
      v_8636 <- evaluateAddress v_2707;
      v_8637 <- getRegister of;
      store v_8636 (mux (eq v_8637 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

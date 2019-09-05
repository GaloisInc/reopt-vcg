def sets1 : instruction :=
  definst "sets" $ do
    pattern fun (v_2759 : reg (bv 8)) => do
      v_4341 <- getRegister sf;
      setRegister (lhs.of_reg v_2759) (mux (eq v_4341 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2751 : Mem) => do
      v_8657 <- evaluateAddress v_2751;
      v_8658 <- getRegister sf;
      store v_8657 (mux (eq v_8658 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

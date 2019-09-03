def setz1 : instruction :=
  definst "setz" $ do
    pattern fun (v_2715 : reg (bv 8)) => do
      v_4297 <- getRegister zf;
      setRegister (lhs.of_reg v_2715) (mux (eq v_4297 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2711 : Mem) => do
      v_9639 <- evaluateAddress v_2711;
      v_9640 <- getRegister zf;
      store v_9639 (mux (eq v_9640 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

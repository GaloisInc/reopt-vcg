def sete1 : instruction :=
  definst "sete" $ do
    pattern fun (v_2506 : reg (bv 8)) => do
      v_3972 <- getRegister zf;
      setRegister (lhs.of_reg v_2506) (mux (eq v_3972 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2498 : Mem) => do
      v_8484 <- evaluateAddress v_2498;
      v_8485 <- getRegister zf;
      store v_8484 (mux (eq v_8485 (expression.bv_nat 1 1)) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

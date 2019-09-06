def seto1 : instruction :=
  definst "seto" $ do
    pattern fun (v_2742 : reg (bv 8)) => do
      v_4241 <- getRegister of;
      setRegister (lhs.of_reg v_2742) (mux v_4241 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2735 : Mem) => do
      v_8035 <- evaluateAddress v_2735;
      v_8036 <- getRegister of;
      store v_8035 (mux v_8036 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

def setpe1 : instruction :=
  definst "setpe" $ do
    pattern fun (v_2764 : reg (bv 8)) => do
      v_4259 <- getRegister pf;
      setRegister (lhs.of_reg v_2764) (mux v_4259 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
    pat_end;
    pattern fun (v_2757 : Mem) => do
      v_8043 <- evaluateAddress v_2757;
      v_8044 <- getRegister pf;
      store v_8043 (mux v_8044 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
    pat_end

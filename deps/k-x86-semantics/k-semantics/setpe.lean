def setpe : instruction :=
  definst "setpe" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- getRegister pf;
      store v_1 (mux v_2 (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister pf;
      setRegister (lhs.of_reg rh_0) (mux v_1 (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
     action

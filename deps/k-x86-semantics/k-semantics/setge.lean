def setge : instruction :=
  definst "setge" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- getRegister sf;
      let v_3 <- getRegister of;
      store v_1 (mux (eq v_2 v_3) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister sf;
      let v_2 <- getRegister of;
      setRegister (lhs.of_reg rh_0) (mux (eq v_1 v_2) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
     action

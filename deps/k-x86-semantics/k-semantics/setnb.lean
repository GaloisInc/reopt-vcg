def setnb : instruction :=
  definst "setnb" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- getRegister cf;
      store v_1 (mux (notBool_ v_2) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister cf;
      setRegister (lhs.of_reg rh_0) (mux (notBool_ v_1) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
     action

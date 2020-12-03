def notb : instruction :=
  definst "notb" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 1;
      store v_1 (bv_xor v_2 (expression.bv_nat 8 255)) 1;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg rh_0);
      setRegister (lhs.of_reg rh_0) (bv_xor v_1 (expression.bv_nat 8 255));
      pure ()
     action

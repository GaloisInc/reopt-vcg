def setle : instruction :=
  definst "setle" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- getRegister zf;
      let v_3 <- getRegister sf;
      let v_4 <- getRegister of;
      store v_1 (mux (bit_or v_2 (notBool_ (eq v_3 v_4))) (expression.bv_nat 8 1) (expression.bv_nat 8 0)) 1;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister zf;
      let v_2 <- getRegister sf;
      let v_3 <- getRegister of;
      setRegister (lhs.of_reg rh_0) (mux (bit_or v_1 (notBool_ (eq v_2 v_3))) (expression.bv_nat 8 1) (expression.bv_nat 8 0));
      pure ()
     action

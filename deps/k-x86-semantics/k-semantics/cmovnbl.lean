def cmovnbl : instruction :=
  definst "cmovnbl" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister cf;
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 4;
      let v_5 <- getRegister (lhs.of_reg r32_1);
      setRegister (lhs.of_reg r32_1) (mux (notBool_ v_2) v_4 v_5);
      pure ()
     action;
    instr_pat $ fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister cf;
      let v_3 <- getRegister (lhs.of_reg r32_0);
      let v_4 <- getRegister (lhs.of_reg r32_1);
      setRegister (lhs.of_reg r32_1) (mux (notBool_ v_2) v_3 v_4);
      pure ()
     action

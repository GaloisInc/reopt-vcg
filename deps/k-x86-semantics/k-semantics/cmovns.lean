def cmovns : instruction :=
  definst "cmovns" $ do
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister sf;
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 2;
      let v_5 <- getRegister (lhs.of_reg r16_1);
      setRegister (lhs.of_reg r16_1) (mux (notBool_ v_2) v_4 v_5);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister sf;
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 4;
      let v_5 <- getRegister (lhs.of_reg r32_1);
      setRegister (lhs.of_reg r32_1) (mux (notBool_ v_2) v_4 v_5);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister sf;
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 8;
      let v_5 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux (notBool_ v_2) v_4 v_5);
      pure ()
     action

def cmovew : instruction :=
  definst "cmovew" $ do
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister zf;
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 2;
      let v_5 <- getRegister (lhs.of_reg r16_1);
      setRegister (lhs.of_reg r16_1) (mux v_2 v_4 v_5);
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister zf;
      let v_3 <- getRegister (lhs.of_reg r16_0);
      let v_4 <- getRegister (lhs.of_reg r16_1);
      setRegister (lhs.of_reg r16_1) (mux v_2 v_3 v_4);
      pure ()
     action

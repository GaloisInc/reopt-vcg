def cmovzq : instruction :=
  definst "cmovzq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister zf;
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 8;
      let v_5 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux v_2 v_4 v_5);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister zf;
      let v_3 <- getRegister (lhs.of_reg r64_0);
      let v_4 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux v_2 v_3 v_4);
      pure ()
     action

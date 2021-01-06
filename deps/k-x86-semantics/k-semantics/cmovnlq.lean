def cmovnlq : instruction :=
  definst "cmovnlq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister sf;
      let v_3 <- getRegister of;
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 8;
      let v_6 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux (eq v_2 v_3) v_5 v_6);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister sf;
      let v_3 <- getRegister of;
      let v_4 <- getRegister (lhs.of_reg r64_0);
      let v_5 <- getRegister (lhs.of_reg r64_1);
      setRegister (lhs.of_reg r64_1) (mux (eq v_2 v_3) v_4 v_5);
      pure ()
     action

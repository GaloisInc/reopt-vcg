def cmovnlw : instruction :=
  definst "cmovnlw" $ do
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister sf;
      let v_3 <- getRegister of;
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 2;
      let v_6 <- getRegister (lhs.of_reg r16_1);
      setRegister (lhs.of_reg r16_1) (mux (eq v_2 v_3) v_5 v_6);
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister sf;
      let v_3 <- getRegister of;
      let v_4 <- getRegister (lhs.of_reg r16_0);
      let v_5 <- getRegister (lhs.of_reg r16_1);
      setRegister (lhs.of_reg r16_1) (mux (eq v_2 v_3) v_4 v_5);
      pure ()
     action

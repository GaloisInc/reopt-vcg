def movsbw : instruction :=
  definst "movsbw" $ do
    instr_pat $ fun (mem_0 : Mem) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 1;
      setRegister (lhs.of_reg r16_1) (sext v_3 16);
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) (r16_1 : reg (bv 16)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg rh_0);
      setRegister (lhs.of_reg r16_1) (sext v_2 16);
      pure ()
     action

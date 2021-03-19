def movsbq : instruction :=
  definst "movsbq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 1;
      setRegister (lhs.of_reg r64_1) (sext v_3 64);
      pure ()
     action;
    instr_pat $ fun (r8_0 : reg (bv 8)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r8_0);
      setRegister (lhs.of_reg r64_1) (sext v_2 64);
      pure ()
     action

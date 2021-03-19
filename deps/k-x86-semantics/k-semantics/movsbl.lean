def movsbl : instruction :=
  definst "movsbl" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 1;
      setRegister (lhs.of_reg r32_1) (sext v_3 32);
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg rh_0);
      setRegister (lhs.of_reg r32_1) (sext v_2 32);
      pure ()
     action

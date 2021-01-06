def notq : instruction :=
  definst "notq" $ do
    instr_pat $ fun (mem_0 : Mem) =>
     let action : semantics Unit := do
      let v_1 <- evaluateAddress mem_0;
      let v_2 <- load v_1 8;
      store v_1 (bv_xor v_2 (expression.bv_nat 64 18446744073709551615)) 8;
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_1 <- getRegister (lhs.of_reg r64_0);
      setRegister (lhs.of_reg r64_0) (bv_xor v_1 (expression.bv_nat 64 18446744073709551615));
      pure ()
     action

def movzbq : instruction :=
  definst "movzbq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 1;
      let v_4 <- eval (concat (expression.bv_nat 56 0) v_3);
      setRegister (lhs.of_reg r64_1) v_4;
      pure ()
     action;
    instr_pat $ fun (r8_0 : reg (bv 8)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r8_0);
      let v_3 <- eval (concat (expression.bv_nat 56 0) v_2);
      setRegister (lhs.of_reg r64_1) v_3;
      pure ()
     action

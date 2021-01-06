def movzwq : instruction :=
  definst "movzwq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 2;
      let v_4 <- eval (concat (expression.bv_nat 48 0) v_3);
      setRegister (lhs.of_reg r64_1) v_4;
      pure ()
     action;
    instr_pat $ fun (r16_0 : reg (bv 16)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r16_0);
      let v_3 <- eval (concat (expression.bv_nat 48 0) v_2);
      setRegister (lhs.of_reg r64_1) v_3;
      pure ()
     action

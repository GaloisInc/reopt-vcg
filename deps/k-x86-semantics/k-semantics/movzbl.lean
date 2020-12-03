def movzbl : instruction :=
  definst "movzbl" $ do
    instr_pat $ fun (mem_0 : Mem) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 1;
      let v_4 <- eval (concat (expression.bv_nat 24 0) v_3);
      setRegister (lhs.of_reg r32_1) v_4;
      pure ()
     action;
    instr_pat $ fun (rh_0 : reg (bv 8)) (r32_1 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg rh_0);
      let v_3 <- eval (concat (expression.bv_nat 24 0) v_2);
      setRegister (lhs.of_reg r32_1) v_3;
      pure ()
     action

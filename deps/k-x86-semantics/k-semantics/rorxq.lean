def rorxq : instruction :=
  definst "rorxq" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_1;
      let v_4 <- load v_3 8;
      let v_5 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8));
      let v_6 <- eval (bv_and v_5 (expression.bv_nat 64 63));
      let (v_7 : expression (bv 64)) <- eval (extract (shl v_4 (sub (expression.bv_nat 64 64) v_6)) 0 64);
      setRegister (lhs.of_reg r64_2) (bv_or (lshr v_4 v_6) v_7);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (r64_1 : reg (bv 64)) (r64_2 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg r64_1);
      let v_4 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8));
      let v_5 <- eval (bv_and v_4 (expression.bv_nat 64 63));
      let (v_6 : expression (bv 64)) <- eval (extract (shl v_3 (sub (expression.bv_nat 64 64) v_5)) 0 64);
      setRegister (lhs.of_reg r64_2) (bv_or (lshr v_3 v_5) v_6);
      pure ()
     action

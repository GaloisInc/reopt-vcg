def vextractps : instruction :=
  definst "vextractps" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_2;
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 2)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8);
      let v_6 <- eval (concat (expression.bv_nat 126 0) v_5);
      let (v_7 : expression (bv 128)) <- eval (extract (shl v_6 (expression.bv_nat 128 5)) 0 128);
      let (v_8 : expression (bv 32)) <- eval (extract (lshr v_4 v_7) 96 128);
      store v_3 v_8 4;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (r32_2 : reg (bv 32)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 2)) <- eval (extract (handleImmediateWithSignExtend imm_0 8 8) 6 8);
      let v_5 <- eval (concat (expression.bv_nat 126 0) v_4);
      let (v_6 : expression (bv 128)) <- eval (extract (shl v_5 (expression.bv_nat 128 5)) 0 128);
      let (v_7 : expression (bv 32)) <- eval (extract (lshr v_3 v_6) 96 128);
      setRegister (lhs.of_reg r32_2) v_7;
      pure ()
     action

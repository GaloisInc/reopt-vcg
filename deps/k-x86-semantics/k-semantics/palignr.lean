def palignr : instruction :=
  definst "palignr" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let v_4 <- evaluateAddress mem_1;
      let v_5 <- load v_4 16;
      let v_6 <- eval (concat v_3 v_5);
      let v_7 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8));
      let (v_8 : expression (bv 256)) <- eval (extract (shl v_7 (expression.bv_nat 256 3)) 0 256);
      let (v_9 : expression (bv 128)) <- eval (extract (lshr v_6 v_8) 128 256);
      setRegister (lhs.of_reg xmm_2) v_9;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_2);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let v_5 <- eval (concat v_3 v_4);
      let v_6 <- eval (concat (expression.bv_nat 248 0) (handleImmediateWithSignExtend imm_0 8 8));
      let (v_7 : expression (bv 256)) <- eval (extract (shl v_6 (expression.bv_nat 256 3)) 0 256);
      let (v_8 : expression (bv 128)) <- eval (extract (lshr v_5 v_7) 128 256);
      setRegister (lhs.of_reg xmm_2) v_8;
      pure ()
     action

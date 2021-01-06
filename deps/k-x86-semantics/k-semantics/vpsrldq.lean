def vpsrldq : instruction :=
  definst "vpsrldq" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_5 <- eval (concat (expression.bv_nat 120 0) v_4);
      let (v_6 : expression (bv 128)) <- eval (extract (shl (mux (ugt v_4 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) v_5) (expression.bv_nat 128 3)) 0 128);
      setRegister (lhs.of_reg xmm_2) (lshr v_3 v_6);
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 128)) <- eval (extract v_3 0 128);
      let v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_6 <- eval (concat (expression.bv_nat 120 0) v_5);
      let (v_7 : expression (bv 128)) <- eval (extract (shl (mux (ugt v_5 (expression.bv_nat 8 15)) (expression.bv_nat 128 16) v_6) (expression.bv_nat 128 3)) 0 128);
      let (v_8 : expression (bv 128)) <- eval (extract v_3 128 256);
      let v_9 <- eval (concat (lshr v_4 v_7) (lshr v_8 v_7));
      setRegister (lhs.of_reg ymm_2) v_9;
      pure ()
     action

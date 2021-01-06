def psrlq : instruction :=
  definst "psrlq" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- eval (concat (expression.bv_nat 56 0) (handleImmediateWithSignExtend imm_0 8 8));
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      let (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_6 <- eval (concat (lshr v_4 v_2) (lshr v_5 v_2));
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_2 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) v_6);
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      let (v_7 : expression (bv 64)) <- eval (extract v_5 64 128);
      let v_8 <- eval (concat (lshr v_6 v_4) (lshr v_7 v_4));
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_4 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) v_8);
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 64)) <- eval (extract v_2 64 128);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 64)) <- eval (extract v_4 0 64);
      let (v_6 : expression (bv 64)) <- eval (extract v_4 64 128);
      let v_7 <- eval (concat (lshr v_5 v_3) (lshr v_6 v_3));
      setRegister (lhs.of_reg xmm_1) (mux (ugt v_3 (expression.bv_nat 64 63)) (expression.bv_nat 128 0) v_7);
      pure ()
     action

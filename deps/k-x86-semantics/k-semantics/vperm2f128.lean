def vperm2f128 : instruction :=
  definst "vperm2f128" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_5 : expression (bv 2)) <- eval (extract v_4 2 4);
      let v_6 <- getRegister (lhs.of_reg ymm_2);
      let (v_7 : expression (bv 128)) <- eval (extract v_6 128 256);
      let (v_8 : expression (bv 128)) <- eval (extract v_6 0 128);
      let v_9 <- evaluateAddress mem_1;
      let v_10 <- load v_9 32;
      let (v_11 : expression (bv 128)) <- eval (extract v_10 128 256);
      let (v_12 : expression (bv 128)) <- eval (extract v_10 0 128);
      let (v_13 : expression (bv 2)) <- eval (extract v_4 6 8);
      let v_14 <- eval (concat (mux (isBitSet v_4 0) (expression.bv_nat 128 0) (mux (eq v_5 (expression.bv_nat 2 0)) v_7 (mux (eq v_5 (expression.bv_nat 2 1)) v_8 (mux (eq v_5 (expression.bv_nat 2 2)) v_11 v_12)))) (mux (isBitSet v_4 4) (expression.bv_nat 128 0) (mux (eq v_13 (expression.bv_nat 2 0)) v_7 (mux (eq v_13 (expression.bv_nat 2 1)) v_8 (mux (eq v_13 (expression.bv_nat 2 2)) v_11 v_12)))));
      setRegister (lhs.of_reg ymm_3) v_14;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let (v_5 : expression (bv 2)) <- eval (extract v_4 2 4);
      let v_6 <- getRegister (lhs.of_reg ymm_2);
      let (v_7 : expression (bv 128)) <- eval (extract v_6 128 256);
      let (v_8 : expression (bv 128)) <- eval (extract v_6 0 128);
      let v_9 <- getRegister (lhs.of_reg ymm_1);
      let (v_10 : expression (bv 128)) <- eval (extract v_9 128 256);
      let (v_11 : expression (bv 128)) <- eval (extract v_9 0 128);
      let (v_12 : expression (bv 2)) <- eval (extract v_4 6 8);
      let v_13 <- eval (concat (mux (isBitSet v_4 0) (expression.bv_nat 128 0) (mux (eq v_5 (expression.bv_nat 2 0)) v_7 (mux (eq v_5 (expression.bv_nat 2 1)) v_8 (mux (eq v_5 (expression.bv_nat 2 2)) v_10 v_11)))) (mux (isBitSet v_4 4) (expression.bv_nat 128 0) (mux (eq v_12 (expression.bv_nat 2 0)) v_7 (mux (eq v_12 (expression.bv_nat 2 1)) v_8 (mux (eq v_12 (expression.bv_nat 2 2)) v_10 v_11)))));
      setRegister (lhs.of_reg ymm_3) v_13;
      pure ()
     action

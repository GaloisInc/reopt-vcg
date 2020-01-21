def vperm2i128 : instruction :=
  definst "vperm2i128" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (extract v_4 2 4);
      v_6 <- getRegister (lhs.of_reg ymm_2);
      v_7 <- eval (extract v_6 128 256);
      v_8 <- eval (extract v_6 0 128);
      v_9 <- evaluateAddress mem_1;
      v_10 <- load v_9 32;
      v_11 <- eval (extract v_10 128 256);
      v_12 <- eval (extract v_10 0 128);
      v_13 <- eval (extract v_4 6 8);
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitSet v_4 0) (expression.bv_nat 128 0) (mux (eq v_5 (expression.bv_nat 2 0)) v_7 (mux (eq v_5 (expression.bv_nat 2 1)) v_8 (mux (eq v_5 (expression.bv_nat 2 2)) v_11 v_12)))) (mux (isBitSet v_4 4) (expression.bv_nat 128 0) (mux (eq v_13 (expression.bv_nat 2 0)) v_7 (mux (eq v_13 (expression.bv_nat 2 1)) v_8 (mux (eq v_13 (expression.bv_nat 2 2)) v_11 v_12)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (extract v_4 2 4);
      v_6 <- getRegister (lhs.of_reg ymm_2);
      v_7 <- eval (extract v_6 128 256);
      v_8 <- eval (extract v_6 0 128);
      v_9 <- getRegister (lhs.of_reg ymm_1);
      v_10 <- eval (extract v_9 128 256);
      v_11 <- eval (extract v_9 0 128);
      v_12 <- eval (extract v_4 6 8);
      setRegister (lhs.of_reg ymm_3) (concat (mux (isBitSet v_4 0) (expression.bv_nat 128 0) (mux (eq v_5 (expression.bv_nat 2 0)) v_7 (mux (eq v_5 (expression.bv_nat 2 1)) v_8 (mux (eq v_5 (expression.bv_nat 2 2)) v_10 v_11)))) (mux (isBitSet v_4 4) (expression.bv_nat 128 0) (mux (eq v_12 (expression.bv_nat 2 0)) v_7 (mux (eq v_12 (expression.bv_nat 2 1)) v_8 (mux (eq v_12 (expression.bv_nat 2 2)) v_10 v_11)))));
      pure ()
    pat_end

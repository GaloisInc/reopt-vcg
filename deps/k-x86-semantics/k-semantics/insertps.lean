def insertps : instruction :=
  definst "insertps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_4 : expression (bv 2)) <- eval (extract v_3 2 4);
      v_5 <- eval (eq v_4 (expression.bv_nat 2 0));
      v_6 <- getRegister (lhs.of_reg xmm_2);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      v_8 <- eval (eq v_4 (expression.bv_nat 2 1));
      v_9 <- eval (eq v_4 (expression.bv_nat 2 2));
      v_10 <- evaluateAddress mem_1;
      v_11 <- load v_10 4;
      (v_12 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_13 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (mux (isBitSet v_3 4) (expression.bv_nat 32 0) (mux v_5 v_7 (mux v_8 v_7 (mux v_9 v_7 v_11)))) (mux (isBitSet v_3 5) (expression.bv_nat 32 0) (mux v_5 v_12 (mux v_8 v_12 (mux v_9 v_11 v_12))))) (mux (isBitSet v_3 6) (expression.bv_nat 32 0) (mux v_5 v_13 (mux v_8 v_11 v_13)))) (mux (isBitSet v_3 7) (expression.bv_nat 32 0) (mux v_5 v_11 v_14)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_4 : expression (bv 2)) <- eval (extract v_3 2 4);
      v_5 <- eval (eq v_4 (expression.bv_nat 2 0));
      v_6 <- getRegister (lhs.of_reg xmm_2);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      v_8 <- eval (eq v_4 (expression.bv_nat 2 1));
      v_9 <- eval (eq v_4 (expression.bv_nat 2 2));
      (v_10 : expression (bv 2)) <- eval (extract v_3 0 2);
      v_11 <- getRegister (lhs.of_reg xmm_1);
      (v_12 : expression (bv 32)) <- eval (extract v_11 96 128);
      (v_13 : expression (bv 32)) <- eval (extract v_11 64 96);
      (v_14 : expression (bv 32)) <- eval (extract v_11 32 64);
      (v_15 : expression (bv 32)) <- eval (extract v_11 0 32);
      v_16 <- eval (mux (eq v_10 (expression.bv_nat 2 0)) v_12 (mux (eq v_10 (expression.bv_nat 2 1)) v_13 (mux (eq v_10 (expression.bv_nat 2 2)) v_14 v_15)));
      (v_17 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_18 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_19 : expression (bv 32)) <- eval (extract v_6 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (mux (isBitSet v_3 4) (expression.bv_nat 32 0) (mux v_5 v_7 (mux v_8 v_7 (mux v_9 v_7 v_16)))) (mux (isBitSet v_3 5) (expression.bv_nat 32 0) (mux v_5 v_17 (mux v_8 v_17 (mux v_9 v_16 v_17))))) (mux (isBitSet v_3 6) (expression.bv_nat 32 0) (mux v_5 v_18 (mux v_8 v_16 v_18)))) (mux (isBitSet v_3 7) (expression.bv_nat 32 0) (mux v_5 v_16 v_19)));
      pure ()
    pat_end

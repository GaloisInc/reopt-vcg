def shufps1 : instruction :=
  definst "shufps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (isBitSet v_3 0);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      v_7 <- eval (extract v_6 0 32);
      v_8 <- eval (extract v_6 64 96);
      v_9 <- eval (extract v_6 32 64);
      v_10 <- eval (extract v_6 96 128);
      v_11 <- eval (isBitSet v_3 2);
      v_12 <- eval (isBitSet v_3 4);
      v_13 <- getRegister xmm_2;
      v_14 <- eval (extract v_13 0 32);
      v_15 <- eval (extract v_13 64 96);
      v_16 <- eval (extract v_13 32 64);
      v_17 <- eval (extract v_13 96 128);
      v_18 <- eval (isBitSet v_3 6);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_3 1) (mux v_4 v_7 v_8) (mux v_4 v_9 v_10)) (concat (mux (isBitSet v_3 3) (mux v_11 v_7 v_8) (mux v_11 v_9 v_10)) (concat (mux (isBitSet v_3 5) (mux v_12 v_14 v_15) (mux v_12 v_16 v_17)) (mux (isBitSet v_3 7) (mux v_18 v_14 v_15) (mux v_18 v_16 v_17)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (isBitSet v_3 0);
      v_5 <- getRegister xmm_1;
      v_6 <- eval (extract v_5 0 32);
      v_7 <- eval (extract v_5 64 96);
      v_8 <- eval (extract v_5 32 64);
      v_9 <- eval (extract v_5 96 128);
      v_10 <- eval (isBitSet v_3 2);
      v_11 <- eval (isBitSet v_3 4);
      v_12 <- getRegister xmm_2;
      v_13 <- eval (extract v_12 0 32);
      v_14 <- eval (extract v_12 64 96);
      v_15 <- eval (extract v_12 32 64);
      v_16 <- eval (extract v_12 96 128);
      v_17 <- eval (isBitSet v_3 6);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_3 1) (mux v_4 v_6 v_7) (mux v_4 v_8 v_9)) (concat (mux (isBitSet v_3 3) (mux v_10 v_6 v_7) (mux v_10 v_8 v_9)) (concat (mux (isBitSet v_3 5) (mux v_11 v_13 v_14) (mux v_11 v_15 v_16)) (mux (isBitSet v_3 7) (mux v_17 v_13 v_14) (mux v_17 v_15 v_16)))));
      pure ()
    pat_end

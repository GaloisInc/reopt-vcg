def vshufps : instruction :=
  definst "vshufps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (isBitSet v_4 0);
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_7 96 128);
      v_12 <- eval (isBitSet v_4 2);
      v_13 <- eval (isBitSet v_4 4);
      v_14 <- getRegister (lhs.of_reg xmm_2);
      (v_15 : expression (bv 32)) <- eval (extract v_14 0 32);
      (v_16 : expression (bv 32)) <- eval (extract v_14 64 96);
      (v_17 : expression (bv 32)) <- eval (extract v_14 32 64);
      (v_18 : expression (bv 32)) <- eval (extract v_14 96 128);
      v_19 <- eval (isBitSet v_4 6);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 1) (mux v_5 v_8 v_9) (mux v_5 v_10 v_11)) (concat (mux (isBitSet v_4 3) (mux v_12 v_8 v_9) (mux v_12 v_10 v_11)) (concat (mux (isBitSet v_4 5) (mux v_13 v_15 v_16) (mux v_13 v_17 v_18)) (mux (isBitSet v_4 7) (mux v_19 v_15 v_16) (mux v_19 v_17 v_18)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (isBitSet v_4 1);
      v_6 <- eval (isBitSet v_4 0);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 32;
      (v_9 : expression (bv 32)) <- eval (extract v_8 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_8 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_12 : expression (bv 32)) <- eval (extract v_8 96 128);
      v_13 <- eval (isBitSet v_4 3);
      v_14 <- eval (isBitSet v_4 2);
      v_15 <- eval (isBitSet v_4 5);
      v_16 <- eval (isBitSet v_4 4);
      v_17 <- getRegister (lhs.of_reg ymm_2);
      (v_18 : expression (bv 32)) <- eval (extract v_17 0 32);
      (v_19 : expression (bv 32)) <- eval (extract v_17 64 96);
      (v_20 : expression (bv 32)) <- eval (extract v_17 32 64);
      (v_21 : expression (bv 32)) <- eval (extract v_17 96 128);
      v_22 <- eval (isBitSet v_4 7);
      v_23 <- eval (isBitSet v_4 6);
      (v_24 : expression (bv 32)) <- eval (extract v_8 128 160);
      (v_25 : expression (bv 32)) <- eval (extract v_8 192 224);
      (v_26 : expression (bv 32)) <- eval (extract v_8 160 192);
      (v_27 : expression (bv 32)) <- eval (extract v_8 224 256);
      (v_28 : expression (bv 32)) <- eval (extract v_17 128 160);
      (v_29 : expression (bv 32)) <- eval (extract v_17 192 224);
      (v_30 : expression (bv 32)) <- eval (extract v_17 160 192);
      (v_31 : expression (bv 32)) <- eval (extract v_17 224 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux v_5 (mux v_6 v_9 v_10) (mux v_6 v_11 v_12)) (concat (mux v_13 (mux v_14 v_9 v_10) (mux v_14 v_11 v_12)) (concat (mux v_15 (mux v_16 v_18 v_19) (mux v_16 v_20 v_21)) (concat (mux v_22 (mux v_23 v_18 v_19) (mux v_23 v_20 v_21)) (concat (mux v_5 (mux v_6 v_24 v_25) (mux v_6 v_26 v_27)) (concat (mux v_13 (mux v_14 v_24 v_25) (mux v_14 v_26 v_27)) (concat (mux v_15 (mux v_16 v_28 v_29) (mux v_16 v_30 v_31)) (mux v_22 (mux v_23 v_28 v_29) (mux v_23 v_30 v_31)))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (isBitSet v_4 0);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_6 96 128);
      v_11 <- eval (isBitSet v_4 2);
      v_12 <- eval (isBitSet v_4 4);
      v_13 <- getRegister (lhs.of_reg xmm_2);
      (v_14 : expression (bv 32)) <- eval (extract v_13 0 32);
      (v_15 : expression (bv 32)) <- eval (extract v_13 64 96);
      (v_16 : expression (bv 32)) <- eval (extract v_13 32 64);
      (v_17 : expression (bv 32)) <- eval (extract v_13 96 128);
      v_18 <- eval (isBitSet v_4 6);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 1) (mux v_5 v_7 v_8) (mux v_5 v_9 v_10)) (concat (mux (isBitSet v_4 3) (mux v_11 v_7 v_8) (mux v_11 v_9 v_10)) (concat (mux (isBitSet v_4 5) (mux v_12 v_14 v_15) (mux v_12 v_16 v_17)) (mux (isBitSet v_4 7) (mux v_18 v_14 v_15) (mux v_18 v_16 v_17)))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) (ymm_3 : reg (bv 256)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- eval (isBitSet v_4 1);
      v_6 <- eval (isBitSet v_4 0);
      v_7 <- getRegister (lhs.of_reg ymm_1);
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_7 64 96);
      (v_10 : expression (bv 32)) <- eval (extract v_7 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_7 96 128);
      v_12 <- eval (isBitSet v_4 3);
      v_13 <- eval (isBitSet v_4 2);
      v_14 <- eval (isBitSet v_4 5);
      v_15 <- eval (isBitSet v_4 4);
      v_16 <- getRegister (lhs.of_reg ymm_2);
      (v_17 : expression (bv 32)) <- eval (extract v_16 0 32);
      (v_18 : expression (bv 32)) <- eval (extract v_16 64 96);
      (v_19 : expression (bv 32)) <- eval (extract v_16 32 64);
      (v_20 : expression (bv 32)) <- eval (extract v_16 96 128);
      v_21 <- eval (isBitSet v_4 7);
      v_22 <- eval (isBitSet v_4 6);
      (v_23 : expression (bv 32)) <- eval (extract v_7 128 160);
      (v_24 : expression (bv 32)) <- eval (extract v_7 192 224);
      (v_25 : expression (bv 32)) <- eval (extract v_7 160 192);
      (v_26 : expression (bv 32)) <- eval (extract v_7 224 256);
      (v_27 : expression (bv 32)) <- eval (extract v_16 128 160);
      (v_28 : expression (bv 32)) <- eval (extract v_16 192 224);
      (v_29 : expression (bv 32)) <- eval (extract v_16 160 192);
      (v_30 : expression (bv 32)) <- eval (extract v_16 224 256);
      setRegister (lhs.of_reg ymm_3) (concat (mux v_5 (mux v_6 v_8 v_9) (mux v_6 v_10 v_11)) (concat (mux v_12 (mux v_13 v_8 v_9) (mux v_13 v_10 v_11)) (concat (mux v_14 (mux v_15 v_17 v_18) (mux v_15 v_19 v_20)) (concat (mux v_21 (mux v_22 v_17 v_18) (mux v_22 v_19 v_20)) (concat (mux v_5 (mux v_6 v_23 v_24) (mux v_6 v_25 v_26)) (concat (mux v_12 (mux v_13 v_23 v_24) (mux v_13 v_25 v_26)) (concat (mux v_14 (mux v_15 v_27 v_28) (mux v_15 v_29 v_30)) (mux v_21 (mux v_22 v_27 v_28) (mux v_22 v_29 v_30)))))))));
      pure ()
    pat_end

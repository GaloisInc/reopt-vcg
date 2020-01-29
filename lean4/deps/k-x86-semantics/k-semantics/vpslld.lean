def vpslld : instruction :=
  definst "vpslld" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- eval (concat (expression.bv_nat 24 0) v_3);
      (v_7 : expression (bv 32)) <- eval (extract (shl v_5 v_6) 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_9 : expression (bv 32)) <- eval (extract (shl v_8 v_6) 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_6) 0 32);
      (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_6) 0 32);
      setRegister (lhs.of_reg xmm_2) (mux (ugt (concat (expression.bv_nat 56 0) v_3) (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat v_7 (concat v_9 (concat v_11 v_13))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg ymm_1);
      (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      v_6 <- eval (concat (expression.bv_nat 24 0) v_3);
      (v_7 : expression (bv 32)) <- eval (extract (shl v_5 v_6) 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      (v_9 : expression (bv 32)) <- eval (extract (shl v_8 v_6) 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_6) 0 32);
      (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_6) 0 32);
      (v_14 : expression (bv 32)) <- eval (extract v_4 128 160);
      (v_15 : expression (bv 32)) <- eval (extract (shl v_14 v_6) 0 32);
      (v_16 : expression (bv 32)) <- eval (extract v_4 160 192);
      (v_17 : expression (bv 32)) <- eval (extract (shl v_16 v_6) 0 32);
      (v_18 : expression (bv 32)) <- eval (extract v_4 192 224);
      (v_19 : expression (bv 32)) <- eval (extract (shl v_18 v_6) 0 32);
      (v_20 : expression (bv 32)) <- eval (extract v_4 224 256);
      (v_21 : expression (bv 32)) <- eval (extract (shl v_20 v_6) 0 32);
      setRegister (lhs.of_reg ymm_2) (mux (ugt (concat (expression.bv_nat 56 0) v_3) (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat v_7 (concat v_9 (concat v_11 (concat v_13 (concat v_15 (concat v_17 (concat v_19 v_21))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_9 : expression (bv 32)) <- eval (extract (shl v_7 v_8) 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_8) 0 32);
      (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_8) 0 32);
      (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      (v_15 : expression (bv 32)) <- eval (extract (shl v_14 v_8) 0 32);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_5 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat v_9 (concat v_11 (concat v_13 v_15))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_4 96 128);
      (v_9 : expression (bv 32)) <- eval (extract (shl v_7 v_8) 0 32);
      (v_10 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_11 : expression (bv 32)) <- eval (extract (shl v_10 v_8) 0 32);
      (v_12 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_13 : expression (bv 32)) <- eval (extract (shl v_12 v_8) 0 32);
      (v_14 : expression (bv 32)) <- eval (extract v_6 96 128);
      (v_15 : expression (bv 32)) <- eval (extract (shl v_14 v_8) 0 32);
      (v_16 : expression (bv 32)) <- eval (extract v_6 128 160);
      (v_17 : expression (bv 32)) <- eval (extract (shl v_16 v_8) 0 32);
      (v_18 : expression (bv 32)) <- eval (extract v_6 160 192);
      (v_19 : expression (bv 32)) <- eval (extract (shl v_18 v_8) 0 32);
      (v_20 : expression (bv 32)) <- eval (extract v_6 192 224);
      (v_21 : expression (bv 32)) <- eval (extract (shl v_20 v_8) 0 32);
      (v_22 : expression (bv 32)) <- eval (extract v_6 224 256);
      (v_23 : expression (bv 32)) <- eval (extract (shl v_22 v_8) 0 32);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_5 (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat v_9 (concat v_11 (concat v_13 (concat v_15 (concat v_17 (concat v_19 (concat v_21 v_23))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract (shl v_6 v_7) 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_7) 0 32);
      (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_7) 0 32);
      (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_14 : expression (bv 32)) <- eval (extract (shl v_13 v_7) 0 32);
      setRegister (lhs.of_reg xmm_2) (mux (ugt v_4 (expression.bv_nat 64 31)) (expression.bv_nat 128 0) (concat v_8 (concat v_10 (concat v_12 v_14))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_8 : expression (bv 32)) <- eval (extract (shl v_6 v_7) 0 32);
      (v_9 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_10 : expression (bv 32)) <- eval (extract (shl v_9 v_7) 0 32);
      (v_11 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_12 : expression (bv 32)) <- eval (extract (shl v_11 v_7) 0 32);
      (v_13 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_14 : expression (bv 32)) <- eval (extract (shl v_13 v_7) 0 32);
      (v_15 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_16 : expression (bv 32)) <- eval (extract (shl v_15 v_7) 0 32);
      (v_17 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_18 : expression (bv 32)) <- eval (extract (shl v_17 v_7) 0 32);
      (v_19 : expression (bv 32)) <- eval (extract v_5 192 224);
      (v_20 : expression (bv 32)) <- eval (extract (shl v_19 v_7) 0 32);
      (v_21 : expression (bv 32)) <- eval (extract v_5 224 256);
      (v_22 : expression (bv 32)) <- eval (extract (shl v_21 v_7) 0 32);
      setRegister (lhs.of_reg ymm_2) (mux (ugt v_4 (expression.bv_nat 64 31)) (expression.bv_nat 256 0) (concat v_8 (concat v_10 (concat v_12 (concat v_14 (concat v_16 (concat v_18 (concat v_20 v_22))))))));
      pure ()
    pat_end

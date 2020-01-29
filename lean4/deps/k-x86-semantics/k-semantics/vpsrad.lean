def vpsrad : instruction :=
  definst "vpsrad" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_6 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_5) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_9 : expression (bv 32)) <- eval (extract v_3 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (ashr v_4 v_6) (concat (ashr v_7 v_6) (concat (ashr v_8 v_6) (ashr v_9 v_6))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_6 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_5) (expression.bv_nat 64 31)) (expression.bv_nat 32 32) (concat (expression.bv_nat 24 0) v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_9 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_10 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_11 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_12 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_13 : expression (bv 32)) <- eval (extract v_3 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (ashr v_4 v_6) (concat (ashr v_7 v_6) (concat (ashr v_8 v_6) (concat (ashr v_9 v_6) (concat (ashr v_10 v_6) (concat (ashr v_11 v_6) (concat (ashr v_12 v_6) (ashr v_13 v_6))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      (v_8 : expression (bv 32)) <- eval (extract v_6 96 128);
      v_9 <- eval (mux (ugt v_7 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_8);
      (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (ashr v_4 v_9) (concat (ashr v_10 v_9) (concat (ashr v_11 v_9) (ashr v_12 v_9))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      (v_8 : expression (bv 32)) <- eval (extract v_6 96 128);
      v_9 <- eval (mux (ugt v_7 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_8);
      (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_11 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_13 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_14 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_15 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_16 : expression (bv 32)) <- eval (extract v_3 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (ashr v_4 v_9) (concat (ashr v_10 v_9) (concat (ashr v_11 v_9) (concat (ashr v_12 v_9) (concat (ashr v_13 v_9) (concat (ashr v_14 v_9) (concat (ashr v_15 v_9) (ashr v_16 v_9))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_7 : expression (bv 32)) <- eval (extract v_5 96 128);
      v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_7);
      (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (ashr v_4 v_8) (concat (ashr v_9 v_8) (concat (ashr v_10 v_8) (ashr v_11 v_8))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_7 : expression (bv 32)) <- eval (extract v_5 96 128);
      v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 31)) (expression.bv_nat 32 32) v_7);
      (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_12 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_13 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_14 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_15 : expression (bv 32)) <- eval (extract v_3 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (ashr v_4 v_8) (concat (ashr v_9 v_8) (concat (ashr v_10 v_8) (concat (ashr v_11 v_8) (concat (ashr v_12 v_8) (concat (ashr v_13 v_8) (concat (ashr v_14 v_8) (ashr v_15 v_8))))))));
      pure ()
    pat_end

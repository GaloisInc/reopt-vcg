def vpsraw : instruction :=
  definst "vpsraw" $ do
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_6 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_5) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_5));
      (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_9 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_10 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_11 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_12 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_13 : expression (bv 16)) <- eval (extract v_3 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (ashr v_4 v_6) (concat (ashr v_7 v_6) (concat (ashr v_8 v_6) (concat (ashr v_9 v_6) (concat (ashr v_10 v_6) (concat (ashr v_11 v_6) (concat (ashr v_12 v_6) (ashr v_13 v_6))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_6 <- eval (mux (ugt (concat (expression.bv_nat 56 0) v_5) (expression.bv_nat 64 15)) (expression.bv_nat 16 16) (concat (expression.bv_nat 8 0) v_5));
      (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_9 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_10 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_11 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_12 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_13 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_14 : expression (bv 16)) <- eval (extract v_3 128 144);
      (v_15 : expression (bv 16)) <- eval (extract v_3 144 160);
      (v_16 : expression (bv 16)) <- eval (extract v_3 160 176);
      (v_17 : expression (bv 16)) <- eval (extract v_3 176 192);
      (v_18 : expression (bv 16)) <- eval (extract v_3 192 208);
      (v_19 : expression (bv 16)) <- eval (extract v_3 208 224);
      (v_20 : expression (bv 16)) <- eval (extract v_3 224 240);
      (v_21 : expression (bv 16)) <- eval (extract v_3 240 256);
      setRegister (lhs.of_reg ymm_2) (concat (ashr v_4 v_6) (concat (ashr v_7 v_6) (concat (ashr v_8 v_6) (concat (ashr v_9 v_6) (concat (ashr v_10 v_6) (concat (ashr v_11 v_6) (concat (ashr v_12 v_6) (concat (ashr v_13 v_6) (concat (ashr v_14 v_6) (concat (ashr v_15 v_6) (concat (ashr v_16 v_6) (concat (ashr v_17 v_6) (concat (ashr v_18 v_6) (concat (ashr v_19 v_6) (concat (ashr v_20 v_6) (ashr v_21 v_6))))))))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      (v_8 : expression (bv 16)) <- eval (extract v_6 112 128);
      v_9 <- eval (mux (ugt v_7 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_8);
      (v_10 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_14 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_15 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_16 : expression (bv 16)) <- eval (extract v_3 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (ashr v_4 v_9) (concat (ashr v_10 v_9) (concat (ashr v_11 v_9) (concat (ashr v_12 v_9) (concat (ashr v_13 v_9) (concat (ashr v_14 v_9) (concat (ashr v_15 v_9) (ashr v_16 v_9))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 64)) <- eval (extract v_6 64 128);
      (v_8 : expression (bv 16)) <- eval (extract v_6 112 128);
      v_9 <- eval (mux (ugt v_7 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_8);
      (v_10 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_11 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_14 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_15 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_16 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_17 : expression (bv 16)) <- eval (extract v_3 128 144);
      (v_18 : expression (bv 16)) <- eval (extract v_3 144 160);
      (v_19 : expression (bv 16)) <- eval (extract v_3 160 176);
      (v_20 : expression (bv 16)) <- eval (extract v_3 176 192);
      (v_21 : expression (bv 16)) <- eval (extract v_3 192 208);
      (v_22 : expression (bv 16)) <- eval (extract v_3 208 224);
      (v_23 : expression (bv 16)) <- eval (extract v_3 224 240);
      (v_24 : expression (bv 16)) <- eval (extract v_3 240 256);
      setRegister (lhs.of_reg ymm_2) (concat (ashr v_4 v_9) (concat (ashr v_10 v_9) (concat (ashr v_11 v_9) (concat (ashr v_12 v_9) (concat (ashr v_13 v_9) (concat (ashr v_14 v_9) (concat (ashr v_15 v_9) (concat (ashr v_16 v_9) (concat (ashr v_17 v_9) (concat (ashr v_18 v_9) (concat (ashr v_19 v_9) (concat (ashr v_20 v_9) (concat (ashr v_21 v_9) (concat (ashr v_22 v_9) (concat (ashr v_23 v_9) (ashr v_24 v_9))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_7 : expression (bv 16)) <- eval (extract v_5 112 128);
      v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_7);
      (v_9 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_14 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_15 : expression (bv 16)) <- eval (extract v_3 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (ashr v_4 v_8) (concat (ashr v_9 v_8) (concat (ashr v_10 v_8) (concat (ashr v_11 v_8) (concat (ashr v_12 v_8) (concat (ashr v_13 v_8) (concat (ashr v_14 v_8) (ashr v_15 v_8))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_7 : expression (bv 16)) <- eval (extract v_5 112 128);
      v_8 <- eval (mux (ugt v_6 (expression.bv_nat 64 15)) (expression.bv_nat 16 16) v_7);
      (v_9 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_13 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_14 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_15 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_16 : expression (bv 16)) <- eval (extract v_3 128 144);
      (v_17 : expression (bv 16)) <- eval (extract v_3 144 160);
      (v_18 : expression (bv 16)) <- eval (extract v_3 160 176);
      (v_19 : expression (bv 16)) <- eval (extract v_3 176 192);
      (v_20 : expression (bv 16)) <- eval (extract v_3 192 208);
      (v_21 : expression (bv 16)) <- eval (extract v_3 208 224);
      (v_22 : expression (bv 16)) <- eval (extract v_3 224 240);
      (v_23 : expression (bv 16)) <- eval (extract v_3 240 256);
      setRegister (lhs.of_reg ymm_2) (concat (ashr v_4 v_8) (concat (ashr v_9 v_8) (concat (ashr v_10 v_8) (concat (ashr v_11 v_8) (concat (ashr v_12 v_8) (concat (ashr v_13 v_8) (concat (ashr v_14 v_8) (concat (ashr v_15 v_8) (concat (ashr v_16 v_8) (concat (ashr v_17 v_8) (concat (ashr v_18 v_8) (concat (ashr v_19 v_8) (concat (ashr v_20 v_8) (concat (ashr v_21 v_8) (concat (ashr v_22 v_8) (ashr v_23 v_8))))))))))))))));
      pure ()
    pat_end

def vpcmpgtd : instruction :=
  definst "vpcmpgtd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_13 : expression (bv 32)) <- eval (extract v_6 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_4 v_7) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_8 v_9) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_10 v_11) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt v_12 v_13) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_8 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_6 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_6 64 96);
      (v_12 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_13 : expression (bv 32)) <- eval (extract v_6 96 128);
      (v_14 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_15 : expression (bv 32)) <- eval (extract v_6 128 160);
      (v_16 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_17 : expression (bv 32)) <- eval (extract v_6 160 192);
      (v_18 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_19 : expression (bv 32)) <- eval (extract v_6 192 224);
      (v_20 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_21 : expression (bv 32)) <- eval (extract v_6 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_4 v_7) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_8 v_9) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_10 v_11) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_12 v_13) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_14 v_15) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_16 v_17) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_18 v_19) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt v_20 v_21) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_10 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_12 : expression (bv 32)) <- eval (extract v_5 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_4 v_6) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_7 v_8) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_9 v_10) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt v_11 v_12) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_8 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_10 : expression (bv 32)) <- eval (extract v_5 64 96);
      (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      (v_12 : expression (bv 32)) <- eval (extract v_5 96 128);
      (v_13 : expression (bv 32)) <- eval (extract v_3 128 160);
      (v_14 : expression (bv 32)) <- eval (extract v_5 128 160);
      (v_15 : expression (bv 32)) <- eval (extract v_3 160 192);
      (v_16 : expression (bv 32)) <- eval (extract v_5 160 192);
      (v_17 : expression (bv 32)) <- eval (extract v_3 192 224);
      (v_18 : expression (bv 32)) <- eval (extract v_5 192 224);
      (v_19 : expression (bv 32)) <- eval (extract v_3 224 256);
      (v_20 : expression (bv 32)) <- eval (extract v_5 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_4 v_6) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_7 v_8) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_9 v_10) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_11 v_12) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_13 v_14) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_15 v_16) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt v_17 v_18) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt v_19 v_20) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))))))));
      pure ()
    pat_end

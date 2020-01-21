def vpermilps : instruction :=
  definst "vpermilps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (extract v_3 0 2);
      v_5 <- evaluateAddress mem_1;
      v_6 <- load v_5 16;
      v_7 <- eval (extract v_6 96 128);
      v_8 <- eval (extract v_6 64 96);
      v_9 <- eval (extract v_6 32 64);
      v_10 <- eval (extract v_6 0 32);
      v_11 <- eval (extract v_3 2 4);
      v_12 <- eval (extract v_3 4 6);
      v_13 <- eval (extract v_3 6 8);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq v_4 (expression.bv_nat 2 0)) v_7 (mux (eq v_4 (expression.bv_nat 2 1)) v_8 (mux (eq v_4 (expression.bv_nat 2 2)) v_9 v_10))) (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_7 (mux (eq v_11 (expression.bv_nat 2 1)) v_8 (mux (eq v_11 (expression.bv_nat 2 2)) v_9 v_10))) (concat (mux (eq v_12 (expression.bv_nat 2 0)) v_7 (mux (eq v_12 (expression.bv_nat 2 1)) v_8 (mux (eq v_12 (expression.bv_nat 2 2)) v_9 v_10))) (mux (eq v_13 (expression.bv_nat 2 0)) v_7 (mux (eq v_13 (expression.bv_nat 2 1)) v_8 (mux (eq v_13 (expression.bv_nat 2 2)) v_9 v_10))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (ymm_2 : reg (bv 256)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (extract v_3 0 2);
      v_5 <- eval (eq v_4 (expression.bv_nat 2 0));
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 32;
      v_8 <- eval (extract v_7 96 128);
      v_9 <- eval (eq v_4 (expression.bv_nat 2 1));
      v_10 <- eval (extract v_7 64 96);
      v_11 <- eval (eq v_4 (expression.bv_nat 2 2));
      v_12 <- eval (extract v_7 32 64);
      v_13 <- eval (extract v_7 0 32);
      v_14 <- eval (extract v_3 2 4);
      v_15 <- eval (eq v_14 (expression.bv_nat 2 0));
      v_16 <- eval (eq v_14 (expression.bv_nat 2 1));
      v_17 <- eval (eq v_14 (expression.bv_nat 2 2));
      v_18 <- eval (extract v_3 4 6);
      v_19 <- eval (eq v_18 (expression.bv_nat 2 0));
      v_20 <- eval (eq v_18 (expression.bv_nat 2 1));
      v_21 <- eval (eq v_18 (expression.bv_nat 2 2));
      v_22 <- eval (extract v_3 6 8);
      v_23 <- eval (eq v_22 (expression.bv_nat 2 0));
      v_24 <- eval (eq v_22 (expression.bv_nat 2 1));
      v_25 <- eval (eq v_22 (expression.bv_nat 2 2));
      v_26 <- eval (extract v_7 224 256);
      v_27 <- eval (extract v_7 192 224);
      v_28 <- eval (extract v_7 160 192);
      v_29 <- eval (extract v_7 128 160);
      setRegister (lhs.of_reg ymm_2) (concat (mux v_5 v_8 (mux v_9 v_10 (mux v_11 v_12 v_13))) (concat (mux v_15 v_8 (mux v_16 v_10 (mux v_17 v_12 v_13))) (concat (mux v_19 v_8 (mux v_20 v_10 (mux v_21 v_12 v_13))) (concat (mux v_23 v_8 (mux v_24 v_10 (mux v_25 v_12 v_13))) (concat (mux v_5 v_26 (mux v_9 v_27 (mux v_11 v_28 v_29))) (concat (mux v_15 v_26 (mux v_16 v_27 (mux v_17 v_28 v_29))) (concat (mux v_19 v_26 (mux v_20 v_27 (mux v_21 v_28 v_29))) (mux v_23 v_26 (mux v_24 v_27 (mux v_25 v_28 v_29))))))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (extract v_3 0 2);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      v_6 <- eval (extract v_5 96 128);
      v_7 <- eval (extract v_5 64 96);
      v_8 <- eval (extract v_5 32 64);
      v_9 <- eval (extract v_5 0 32);
      v_10 <- eval (extract v_3 2 4);
      v_11 <- eval (extract v_3 4 6);
      v_12 <- eval (extract v_3 6 8);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq v_4 (expression.bv_nat 2 0)) v_6 (mux (eq v_4 (expression.bv_nat 2 1)) v_7 (mux (eq v_4 (expression.bv_nat 2 2)) v_8 v_9))) (concat (mux (eq v_10 (expression.bv_nat 2 0)) v_6 (mux (eq v_10 (expression.bv_nat 2 1)) v_7 (mux (eq v_10 (expression.bv_nat 2 2)) v_8 v_9))) (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_6 (mux (eq v_11 (expression.bv_nat 2 1)) v_7 (mux (eq v_11 (expression.bv_nat 2 2)) v_8 v_9))) (mux (eq v_12 (expression.bv_nat 2 0)) v_6 (mux (eq v_12 (expression.bv_nat 2 1)) v_7 (mux (eq v_12 (expression.bv_nat 2 2)) v_8 v_9))))));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (extract v_3 0 2);
      v_5 <- eval (eq v_4 (expression.bv_nat 2 0));
      v_6 <- getRegister (lhs.of_reg ymm_1);
      v_7 <- eval (extract v_6 96 128);
      v_8 <- eval (eq v_4 (expression.bv_nat 2 1));
      v_9 <- eval (extract v_6 64 96);
      v_10 <- eval (eq v_4 (expression.bv_nat 2 2));
      v_11 <- eval (extract v_6 32 64);
      v_12 <- eval (extract v_6 0 32);
      v_13 <- eval (extract v_3 2 4);
      v_14 <- eval (eq v_13 (expression.bv_nat 2 0));
      v_15 <- eval (eq v_13 (expression.bv_nat 2 1));
      v_16 <- eval (eq v_13 (expression.bv_nat 2 2));
      v_17 <- eval (extract v_3 4 6);
      v_18 <- eval (eq v_17 (expression.bv_nat 2 0));
      v_19 <- eval (eq v_17 (expression.bv_nat 2 1));
      v_20 <- eval (eq v_17 (expression.bv_nat 2 2));
      v_21 <- eval (extract v_3 6 8);
      v_22 <- eval (eq v_21 (expression.bv_nat 2 0));
      v_23 <- eval (eq v_21 (expression.bv_nat 2 1));
      v_24 <- eval (eq v_21 (expression.bv_nat 2 2));
      v_25 <- eval (extract v_6 224 256);
      v_26 <- eval (extract v_6 192 224);
      v_27 <- eval (extract v_6 160 192);
      v_28 <- eval (extract v_6 128 160);
      setRegister (lhs.of_reg ymm_2) (concat (mux v_5 v_7 (mux v_8 v_9 (mux v_10 v_11 v_12))) (concat (mux v_14 v_7 (mux v_15 v_9 (mux v_16 v_11 v_12))) (concat (mux v_18 v_7 (mux v_19 v_9 (mux v_20 v_11 v_12))) (concat (mux v_22 v_7 (mux v_23 v_9 (mux v_24 v_11 v_12))) (concat (mux v_5 v_25 (mux v_8 v_26 (mux v_10 v_27 v_28))) (concat (mux v_14 v_25 (mux v_15 v_26 (mux v_16 v_27 v_28))) (concat (mux v_18 v_25 (mux v_19 v_26 (mux v_20 v_27 v_28))) (mux v_22 v_25 (mux v_23 v_26 (mux v_24 v_27 v_28))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (extract v_4 30 32);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      v_7 <- eval (extract v_6 96 128);
      v_8 <- eval (extract v_6 64 96);
      v_9 <- eval (extract v_6 32 64);
      v_10 <- eval (extract v_6 0 32);
      v_11 <- eval (extract v_4 62 64);
      v_12 <- eval (extract v_4 94 96);
      v_13 <- eval (extract v_4 126 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq v_5 (expression.bv_nat 2 0)) v_7 (mux (eq v_5 (expression.bv_nat 2 1)) v_8 (mux (eq v_5 (expression.bv_nat 2 2)) v_9 v_10))) (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_7 (mux (eq v_11 (expression.bv_nat 2 1)) v_8 (mux (eq v_11 (expression.bv_nat 2 2)) v_9 v_10))) (concat (mux (eq v_12 (expression.bv_nat 2 0)) v_7 (mux (eq v_12 (expression.bv_nat 2 1)) v_8 (mux (eq v_12 (expression.bv_nat 2 2)) v_9 v_10))) (mux (eq v_13 (expression.bv_nat 2 0)) v_7 (mux (eq v_13 (expression.bv_nat 2 1)) v_8 (mux (eq v_13 (expression.bv_nat 2 2)) v_9 v_10))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- eval (extract v_4 30 32);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      v_7 <- eval (extract v_6 96 128);
      v_8 <- eval (extract v_6 64 96);
      v_9 <- eval (extract v_6 32 64);
      v_10 <- eval (extract v_6 0 32);
      v_11 <- eval (extract v_4 62 64);
      v_12 <- eval (extract v_4 94 96);
      v_13 <- eval (extract v_4 126 128);
      v_14 <- eval (extract v_4 158 160);
      v_15 <- eval (extract v_6 224 256);
      v_16 <- eval (extract v_6 192 224);
      v_17 <- eval (extract v_6 160 192);
      v_18 <- eval (extract v_6 128 160);
      v_19 <- eval (extract v_4 190 192);
      v_20 <- eval (extract v_4 222 224);
      v_21 <- eval (extract v_4 254 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (eq v_5 (expression.bv_nat 2 0)) v_7 (mux (eq v_5 (expression.bv_nat 2 1)) v_8 (mux (eq v_5 (expression.bv_nat 2 2)) v_9 v_10))) (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_7 (mux (eq v_11 (expression.bv_nat 2 1)) v_8 (mux (eq v_11 (expression.bv_nat 2 2)) v_9 v_10))) (concat (mux (eq v_12 (expression.bv_nat 2 0)) v_7 (mux (eq v_12 (expression.bv_nat 2 1)) v_8 (mux (eq v_12 (expression.bv_nat 2 2)) v_9 v_10))) (concat (mux (eq v_13 (expression.bv_nat 2 0)) v_7 (mux (eq v_13 (expression.bv_nat 2 1)) v_8 (mux (eq v_13 (expression.bv_nat 2 2)) v_9 v_10))) (concat (mux (eq v_14 (expression.bv_nat 2 0)) v_15 (mux (eq v_14 (expression.bv_nat 2 1)) v_16 (mux (eq v_14 (expression.bv_nat 2 2)) v_17 v_18))) (concat (mux (eq v_19 (expression.bv_nat 2 0)) v_15 (mux (eq v_19 (expression.bv_nat 2 1)) v_16 (mux (eq v_19 (expression.bv_nat 2 2)) v_17 v_18))) (concat (mux (eq v_20 (expression.bv_nat 2 0)) v_15 (mux (eq v_20 (expression.bv_nat 2 1)) v_16 (mux (eq v_20 (expression.bv_nat 2 2)) v_17 v_18))) (mux (eq v_21 (expression.bv_nat 2 0)) v_15 (mux (eq v_21 (expression.bv_nat 2 1)) v_16 (mux (eq v_21 (expression.bv_nat 2 2)) v_17 v_18))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (extract v_3 30 32);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      v_6 <- eval (extract v_5 96 128);
      v_7 <- eval (extract v_5 64 96);
      v_8 <- eval (extract v_5 32 64);
      v_9 <- eval (extract v_5 0 32);
      v_10 <- eval (extract v_3 62 64);
      v_11 <- eval (extract v_3 94 96);
      v_12 <- eval (extract v_3 126 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (eq v_4 (expression.bv_nat 2 0)) v_6 (mux (eq v_4 (expression.bv_nat 2 1)) v_7 (mux (eq v_4 (expression.bv_nat 2 2)) v_8 v_9))) (concat (mux (eq v_10 (expression.bv_nat 2 0)) v_6 (mux (eq v_10 (expression.bv_nat 2 1)) v_7 (mux (eq v_10 (expression.bv_nat 2 2)) v_8 v_9))) (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_6 (mux (eq v_11 (expression.bv_nat 2 1)) v_7 (mux (eq v_11 (expression.bv_nat 2 2)) v_8 v_9))) (mux (eq v_12 (expression.bv_nat 2 0)) v_6 (mux (eq v_12 (expression.bv_nat 2 1)) v_7 (mux (eq v_12 (expression.bv_nat 2 2)) v_8 v_9))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- eval (extract v_3 30 32);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      v_6 <- eval (extract v_5 96 128);
      v_7 <- eval (extract v_5 64 96);
      v_8 <- eval (extract v_5 32 64);
      v_9 <- eval (extract v_5 0 32);
      v_10 <- eval (extract v_3 62 64);
      v_11 <- eval (extract v_3 94 96);
      v_12 <- eval (extract v_3 126 128);
      v_13 <- eval (extract v_3 158 160);
      v_14 <- eval (extract v_5 224 256);
      v_15 <- eval (extract v_5 192 224);
      v_16 <- eval (extract v_5 160 192);
      v_17 <- eval (extract v_5 128 160);
      v_18 <- eval (extract v_3 190 192);
      v_19 <- eval (extract v_3 222 224);
      v_20 <- eval (extract v_3 254 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (eq v_4 (expression.bv_nat 2 0)) v_6 (mux (eq v_4 (expression.bv_nat 2 1)) v_7 (mux (eq v_4 (expression.bv_nat 2 2)) v_8 v_9))) (concat (mux (eq v_10 (expression.bv_nat 2 0)) v_6 (mux (eq v_10 (expression.bv_nat 2 1)) v_7 (mux (eq v_10 (expression.bv_nat 2 2)) v_8 v_9))) (concat (mux (eq v_11 (expression.bv_nat 2 0)) v_6 (mux (eq v_11 (expression.bv_nat 2 1)) v_7 (mux (eq v_11 (expression.bv_nat 2 2)) v_8 v_9))) (concat (mux (eq v_12 (expression.bv_nat 2 0)) v_6 (mux (eq v_12 (expression.bv_nat 2 1)) v_7 (mux (eq v_12 (expression.bv_nat 2 2)) v_8 v_9))) (concat (mux (eq v_13 (expression.bv_nat 2 0)) v_14 (mux (eq v_13 (expression.bv_nat 2 1)) v_15 (mux (eq v_13 (expression.bv_nat 2 2)) v_16 v_17))) (concat (mux (eq v_18 (expression.bv_nat 2 0)) v_14 (mux (eq v_18 (expression.bv_nat 2 1)) v_15 (mux (eq v_18 (expression.bv_nat 2 2)) v_16 v_17))) (concat (mux (eq v_19 (expression.bv_nat 2 0)) v_14 (mux (eq v_19 (expression.bv_nat 2 1)) v_15 (mux (eq v_19 (expression.bv_nat 2 2)) v_16 v_17))) (mux (eq v_20 (expression.bv_nat 2 0)) v_14 (mux (eq v_20 (expression.bv_nat 2 1)) v_15 (mux (eq v_20 (expression.bv_nat 2 2)) v_16 v_17))))))))));
      pure ()
    pat_end

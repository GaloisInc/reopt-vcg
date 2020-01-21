def vpackusdw : instruction :=
  definst "vpackusdw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (extract v_4 0 32);
      v_6 <- eval (extract v_4 32 64);
      v_7 <- eval (extract v_4 64 96);
      v_8 <- eval (extract v_4 96 128);
      v_9 <- getRegister (lhs.of_reg xmm_1);
      v_10 <- eval (extract v_9 0 32);
      v_11 <- eval (extract v_9 32 64);
      v_12 <- eval (extract v_9 64 96);
      v_13 <- eval (extract v_9 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_5 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 48 64))) (concat (mux (sgt v_7 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 80 96))) (concat (mux (sgt v_8 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_8 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 112 128))) (concat (mux (sgt v_10 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 16 32))) (concat (mux (sgt v_11 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 48 64))) (concat (mux (sgt v_12 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 80 96))) (mux (sgt v_13 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_13 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- eval (extract v_4 0 32);
      v_6 <- eval (extract v_4 32 64);
      v_7 <- eval (extract v_4 64 96);
      v_8 <- eval (extract v_4 96 128);
      v_9 <- getRegister (lhs.of_reg ymm_1);
      v_10 <- eval (extract v_9 0 32);
      v_11 <- eval (extract v_9 32 64);
      v_12 <- eval (extract v_9 64 96);
      v_13 <- eval (extract v_9 96 128);
      v_14 <- eval (extract v_4 128 160);
      v_15 <- eval (extract v_4 160 192);
      v_16 <- eval (extract v_4 192 224);
      v_17 <- eval (extract v_4 224 256);
      v_18 <- eval (extract v_9 128 160);
      v_19 <- eval (extract v_9 160 192);
      v_20 <- eval (extract v_9 192 224);
      v_21 <- eval (extract v_9 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_5 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 48 64))) (concat (mux (sgt v_7 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 80 96))) (concat (mux (sgt v_8 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_8 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 112 128))) (concat (mux (sgt v_10 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 16 32))) (concat (mux (sgt v_11 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 48 64))) (concat (mux (sgt v_12 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 80 96))) (concat (mux (sgt v_13 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_13 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 112 128))) (concat (mux (sgt v_14 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_14 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 144 160))) (concat (mux (sgt v_15 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_15 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 176 192))) (concat (mux (sgt v_16 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_16 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 208 224))) (concat (mux (sgt v_17 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_17 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_4 240 256))) (concat (mux (sgt v_18 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_18 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 144 160))) (concat (mux (sgt v_19 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_19 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 176 192))) (concat (mux (sgt v_20 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_20 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 208 224))) (mux (sgt v_21 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_21 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (extract v_3 0 32);
      v_5 <- eval (extract v_3 32 64);
      v_6 <- eval (extract v_3 64 96);
      v_7 <- eval (extract v_3 96 128);
      v_8 <- getRegister (lhs.of_reg xmm_1);
      v_9 <- eval (extract v_8 0 32);
      v_10 <- eval (extract v_8 32 64);
      v_11 <- eval (extract v_8 64 96);
      v_12 <- eval (extract v_8 96 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_4 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_4 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 16 32))) (concat (mux (sgt v_5 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 48 64))) (concat (mux (sgt v_6 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 80 96))) (concat (mux (sgt v_7 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 112 128))) (concat (mux (sgt v_9 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 48 64))) (concat (mux (sgt v_11 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 80 96))) (mux (sgt v_12 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- eval (extract v_3 0 32);
      v_5 <- eval (extract v_3 32 64);
      v_6 <- eval (extract v_3 64 96);
      v_7 <- eval (extract v_3 96 128);
      v_8 <- getRegister (lhs.of_reg ymm_1);
      v_9 <- eval (extract v_8 0 32);
      v_10 <- eval (extract v_8 32 64);
      v_11 <- eval (extract v_8 64 96);
      v_12 <- eval (extract v_8 96 128);
      v_13 <- eval (extract v_3 128 160);
      v_14 <- eval (extract v_3 160 192);
      v_15 <- eval (extract v_3 192 224);
      v_16 <- eval (extract v_3 224 256);
      v_17 <- eval (extract v_8 128 160);
      v_18 <- eval (extract v_8 160 192);
      v_19 <- eval (extract v_8 192 224);
      v_20 <- eval (extract v_8 224 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_4 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_4 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 16 32))) (concat (mux (sgt v_5 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 48 64))) (concat (mux (sgt v_6 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 80 96))) (concat (mux (sgt v_7 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 112 128))) (concat (mux (sgt v_9 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 48 64))) (concat (mux (sgt v_11 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 80 96))) (concat (mux (sgt v_12 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_12 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 112 128))) (concat (mux (sgt v_13 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_13 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 144 160))) (concat (mux (sgt v_14 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_14 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 176 192))) (concat (mux (sgt v_15 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_15 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 208 224))) (concat (mux (sgt v_16 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_16 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_3 240 256))) (concat (mux (sgt v_17 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_17 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 144 160))) (concat (mux (sgt v_18 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_18 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 176 192))) (concat (mux (sgt v_19 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_19 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 208 224))) (mux (sgt v_20 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_20 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_8 240 256))))))))))))))))));
      pure ()
    pat_end

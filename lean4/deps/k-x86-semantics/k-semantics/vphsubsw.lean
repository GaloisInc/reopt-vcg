def vphsubsw : instruction :=
  definst "vphsubsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (sub (sext (extract v_4 16 32) 32) (sext (extract v_4 0 16) 32));
      v_6 <- eval (sub (sext (extract v_4 48 64) 32) (sext (extract v_4 32 48) 32));
      v_7 <- eval (sub (sext (extract v_4 80 96) 32) (sext (extract v_4 64 80) 32));
      v_8 <- eval (sub (sext (extract v_4 112 128) 32) (sext (extract v_4 96 112) 32));
      v_9 <- getRegister (lhs.of_reg xmm_1);
      v_10 <- eval (sub (sext (extract v_9 16 32) 32) (sext (extract v_9 0 16) 32));
      v_11 <- eval (sub (sext (extract v_9 48 64) 32) (sext (extract v_9 32 48) 32));
      v_12 <- eval (sub (sext (extract v_9 80 96) 32) (sext (extract v_9 64 80) 32));
      v_13 <- eval (sub (sext (extract v_9 112 128) 32) (sext (extract v_9 96 112) 32));
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6 16 32))) (concat (mux (sgt v_7 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 16 32))) (concat (mux (sgt v_8 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10 16 32))) (concat (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11 16 32))) (concat (mux (sgt v_12 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12 16 32))) (mux (sgt v_13 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- eval (sub (sext (extract v_4 16 32) 32) (sext (extract v_4 0 16) 32));
      v_6 <- eval (sub (sext (extract v_4 48 64) 32) (sext (extract v_4 32 48) 32));
      v_7 <- eval (sub (sext (extract v_4 80 96) 32) (sext (extract v_4 64 80) 32));
      v_8 <- eval (sub (sext (extract v_4 112 128) 32) (sext (extract v_4 96 112) 32));
      v_9 <- getRegister (lhs.of_reg ymm_1);
      v_10 <- eval (sub (sext (extract v_9 16 32) 32) (sext (extract v_9 0 16) 32));
      v_11 <- eval (sub (sext (extract v_9 48 64) 32) (sext (extract v_9 32 48) 32));
      v_12 <- eval (sub (sext (extract v_9 80 96) 32) (sext (extract v_9 64 80) 32));
      v_13 <- eval (sub (sext (extract v_9 112 128) 32) (sext (extract v_9 96 112) 32));
      v_14 <- eval (sub (sext (extract v_4 144 160) 32) (sext (extract v_4 128 144) 32));
      v_15 <- eval (sub (sext (extract v_4 176 192) 32) (sext (extract v_4 160 176) 32));
      v_16 <- eval (sub (sext (extract v_4 208 224) 32) (sext (extract v_4 192 208) 32));
      v_17 <- eval (sub (sext (extract v_4 240 256) 32) (sext (extract v_4 224 240) 32));
      v_18 <- eval (sub (sext (extract v_9 144 160) 32) (sext (extract v_9 128 144) 32));
      v_19 <- eval (sub (sext (extract v_9 176 192) 32) (sext (extract v_9 160 176) 32));
      v_20 <- eval (sub (sext (extract v_9 208 224) 32) (sext (extract v_9 192 208) 32));
      v_21 <- eval (sub (sext (extract v_9 240 256) 32) (sext (extract v_9 224 240) 32));
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6 16 32))) (concat (mux (sgt v_7 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 16 32))) (concat (mux (sgt v_8 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10 16 32))) (concat (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11 16 32))) (concat (mux (sgt v_12 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12 16 32))) (concat (mux (sgt v_13 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13 16 32))) (concat (mux (sgt v_14 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_14 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_14 16 32))) (concat (mux (sgt v_15 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_15 16 32))) (concat (mux (sgt v_16 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_16 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_16 16 32))) (concat (mux (sgt v_17 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17 16 32))) (concat (mux (sgt v_18 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18 16 32))) (concat (mux (sgt v_19 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_19 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_19 16 32))) (concat (mux (sgt v_20 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_20 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_20 16 32))) (mux (sgt v_21 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_21 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_21 16 32))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (sub (sext (extract v_3 16 32) 32) (sext (extract v_3 0 16) 32));
      v_5 <- eval (sub (sext (extract v_3 48 64) 32) (sext (extract v_3 32 48) 32));
      v_6 <- eval (sub (sext (extract v_3 80 96) 32) (sext (extract v_3 64 80) 32));
      v_7 <- eval (sub (sext (extract v_3 112 128) 32) (sext (extract v_3 96 112) 32));
      v_8 <- getRegister (lhs.of_reg xmm_1);
      v_9 <- eval (sub (sext (extract v_8 16 32) 32) (sext (extract v_8 0 16) 32));
      v_10 <- eval (sub (sext (extract v_8 48 64) 32) (sext (extract v_8 32 48) 32));
      v_11 <- eval (sub (sext (extract v_8 80 96) 32) (sext (extract v_8 64 80) 32));
      v_12 <- eval (sub (sext (extract v_8 112 128) 32) (sext (extract v_8 96 112) 32));
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_4 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4 16 32))) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6 16 32))) (concat (mux (sgt v_7 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 16 32))) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10 16 32))) (concat (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11 16 32))) (mux (sgt v_12 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- eval (sub (sext (extract v_3 16 32) 32) (sext (extract v_3 0 16) 32));
      v_5 <- eval (sub (sext (extract v_3 48 64) 32) (sext (extract v_3 32 48) 32));
      v_6 <- eval (sub (sext (extract v_3 80 96) 32) (sext (extract v_3 64 80) 32));
      v_7 <- eval (sub (sext (extract v_3 112 128) 32) (sext (extract v_3 96 112) 32));
      v_8 <- getRegister (lhs.of_reg ymm_1);
      v_9 <- eval (sub (sext (extract v_8 16 32) 32) (sext (extract v_8 0 16) 32));
      v_10 <- eval (sub (sext (extract v_8 48 64) 32) (sext (extract v_8 32 48) 32));
      v_11 <- eval (sub (sext (extract v_8 80 96) 32) (sext (extract v_8 64 80) 32));
      v_12 <- eval (sub (sext (extract v_8 112 128) 32) (sext (extract v_8 96 112) 32));
      v_13 <- eval (sub (sext (extract v_3 144 160) 32) (sext (extract v_3 128 144) 32));
      v_14 <- eval (sub (sext (extract v_3 176 192) 32) (sext (extract v_3 160 176) 32));
      v_15 <- eval (sub (sext (extract v_3 208 224) 32) (sext (extract v_3 192 208) 32));
      v_16 <- eval (sub (sext (extract v_3 240 256) 32) (sext (extract v_3 224 240) 32));
      v_17 <- eval (sub (sext (extract v_8 144 160) 32) (sext (extract v_8 128 144) 32));
      v_18 <- eval (sub (sext (extract v_8 176 192) 32) (sext (extract v_8 160 176) 32));
      v_19 <- eval (sub (sext (extract v_8 208 224) 32) (sext (extract v_8 192 208) 32));
      v_20 <- eval (sub (sext (extract v_8 240 256) 32) (sext (extract v_8 224 240) 32));
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_4 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4 16 32))) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6 16 32))) (concat (mux (sgt v_7 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 16 32))) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10 16 32))) (concat (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11 16 32))) (concat (mux (sgt v_12 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12 16 32))) (concat (mux (sgt v_13 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13 16 32))) (concat (mux (sgt v_14 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_14 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_14 16 32))) (concat (mux (sgt v_15 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_15 16 32))) (concat (mux (sgt v_16 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_16 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_16 16 32))) (concat (mux (sgt v_17 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_17 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_17 16 32))) (concat (mux (sgt v_18 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_18 16 32))) (concat (mux (sgt v_19 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_19 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_19 16 32))) (mux (sgt v_20 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_20 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_20 16 32))))))))))))))))));
      pure ()
    pat_end

def vpsubsw : instruction :=
  definst "vpsubsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- eval (sub (sext (extract v_3 0 16) 18) (sext (extract v_5 0 16) 18));
      v_7 <- eval (sub (sext (extract v_3 16 32) 18) (sext (extract v_5 16 32) 18));
      v_8 <- eval (sub (sext (extract v_3 32 48) 18) (sext (extract v_5 32 48) 18));
      v_9 <- eval (sub (sext (extract v_3 48 64) 18) (sext (extract v_5 48 64) 18));
      v_10 <- eval (sub (sext (extract v_3 64 80) 18) (sext (extract v_5 64 80) 18));
      v_11 <- eval (sub (sext (extract v_3 80 96) 18) (sext (extract v_5 80 96) 18));
      v_12 <- eval (sub (sext (extract v_3 96 112) 18) (sext (extract v_5 96 112) 18));
      v_13 <- eval (sub (sext (extract v_3 112 128) 18) (sext (extract v_5 112 128) 18));
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_6 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_6 2 18))) (concat (mux (sgt v_7 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_7 2 18))) (concat (mux (sgt v_8 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8 2 18))) (concat (mux (sgt v_9 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_9 2 18))) (concat (mux (sgt v_10 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10 2 18))) (concat (mux (sgt v_11 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11 2 18))) (concat (mux (sgt v_12 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_12 2 18))) (mux (sgt v_13 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_13 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_13 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 32;
      v_6 <- eval (sub (sext (extract v_3 0 16) 18) (sext (extract v_5 0 16) 18));
      v_7 <- eval (sub (sext (extract v_3 16 32) 18) (sext (extract v_5 16 32) 18));
      v_8 <- eval (sub (sext (extract v_3 32 48) 18) (sext (extract v_5 32 48) 18));
      v_9 <- eval (sub (sext (extract v_3 48 64) 18) (sext (extract v_5 48 64) 18));
      v_10 <- eval (sub (sext (extract v_3 64 80) 18) (sext (extract v_5 64 80) 18));
      v_11 <- eval (sub (sext (extract v_3 80 96) 18) (sext (extract v_5 80 96) 18));
      v_12 <- eval (sub (sext (extract v_3 96 112) 18) (sext (extract v_5 96 112) 18));
      v_13 <- eval (sub (sext (extract v_3 112 128) 18) (sext (extract v_5 112 128) 18));
      v_14 <- eval (sub (sext (extract v_3 128 144) 18) (sext (extract v_5 128 144) 18));
      v_15 <- eval (sub (sext (extract v_3 144 160) 18) (sext (extract v_5 144 160) 18));
      v_16 <- eval (sub (sext (extract v_3 160 176) 18) (sext (extract v_5 160 176) 18));
      v_17 <- eval (sub (sext (extract v_3 176 192) 18) (sext (extract v_5 176 192) 18));
      v_18 <- eval (sub (sext (extract v_3 192 208) 18) (sext (extract v_5 192 208) 18));
      v_19 <- eval (sub (sext (extract v_3 208 224) 18) (sext (extract v_5 208 224) 18));
      v_20 <- eval (sub (sext (extract v_3 224 240) 18) (sext (extract v_5 224 240) 18));
      v_21 <- eval (sub (sext (extract v_3 240 256) 18) (sext (extract v_5 240 256) 18));
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_6 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_6 2 18))) (concat (mux (sgt v_7 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_7 2 18))) (concat (mux (sgt v_8 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8 2 18))) (concat (mux (sgt v_9 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_9 2 18))) (concat (mux (sgt v_10 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10 2 18))) (concat (mux (sgt v_11 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11 2 18))) (concat (mux (sgt v_12 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_12 2 18))) (concat (mux (sgt v_13 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_13 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_13 2 18))) (concat (mux (sgt v_14 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14 2 18))) (concat (mux (sgt v_15 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15 2 18))) (concat (mux (sgt v_16 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_16 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_16 2 18))) (concat (mux (sgt v_17 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_17 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_17 2 18))) (concat (mux (sgt v_18 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_18 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_18 2 18))) (concat (mux (sgt v_19 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_19 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_19 2 18))) (concat (mux (sgt v_20 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_20 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_20 2 18))) (mux (sgt v_21 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_21 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_21 2 18))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- eval (sub (sext (extract v_3 0 16) 18) (sext (extract v_4 0 16) 18));
      v_6 <- eval (sub (sext (extract v_3 16 32) 18) (sext (extract v_4 16 32) 18));
      v_7 <- eval (sub (sext (extract v_3 32 48) 18) (sext (extract v_4 32 48) 18));
      v_8 <- eval (sub (sext (extract v_3 48 64) 18) (sext (extract v_4 48 64) 18));
      v_9 <- eval (sub (sext (extract v_3 64 80) 18) (sext (extract v_4 64 80) 18));
      v_10 <- eval (sub (sext (extract v_3 80 96) 18) (sext (extract v_4 80 96) 18));
      v_11 <- eval (sub (sext (extract v_3 96 112) 18) (sext (extract v_4 96 112) 18));
      v_12 <- eval (sub (sext (extract v_3 112 128) 18) (sext (extract v_4 112 128) 18));
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_5 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5 2 18))) (concat (mux (sgt v_6 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_6 2 18))) (concat (mux (sgt v_7 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_7 2 18))) (concat (mux (sgt v_8 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8 2 18))) (concat (mux (sgt v_9 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_9 2 18))) (concat (mux (sgt v_10 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10 2 18))) (concat (mux (sgt v_11 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11 2 18))) (mux (sgt v_12 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_12 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- getRegister (lhs.of_reg ymm_0);
      v_5 <- eval (sub (sext (extract v_3 0 16) 18) (sext (extract v_4 0 16) 18));
      v_6 <- eval (sub (sext (extract v_3 16 32) 18) (sext (extract v_4 16 32) 18));
      v_7 <- eval (sub (sext (extract v_3 32 48) 18) (sext (extract v_4 32 48) 18));
      v_8 <- eval (sub (sext (extract v_3 48 64) 18) (sext (extract v_4 48 64) 18));
      v_9 <- eval (sub (sext (extract v_3 64 80) 18) (sext (extract v_4 64 80) 18));
      v_10 <- eval (sub (sext (extract v_3 80 96) 18) (sext (extract v_4 80 96) 18));
      v_11 <- eval (sub (sext (extract v_3 96 112) 18) (sext (extract v_4 96 112) 18));
      v_12 <- eval (sub (sext (extract v_3 112 128) 18) (sext (extract v_4 112 128) 18));
      v_13 <- eval (sub (sext (extract v_3 128 144) 18) (sext (extract v_4 128 144) 18));
      v_14 <- eval (sub (sext (extract v_3 144 160) 18) (sext (extract v_4 144 160) 18));
      v_15 <- eval (sub (sext (extract v_3 160 176) 18) (sext (extract v_4 160 176) 18));
      v_16 <- eval (sub (sext (extract v_3 176 192) 18) (sext (extract v_4 176 192) 18));
      v_17 <- eval (sub (sext (extract v_3 192 208) 18) (sext (extract v_4 192 208) 18));
      v_18 <- eval (sub (sext (extract v_3 208 224) 18) (sext (extract v_4 208 224) 18));
      v_19 <- eval (sub (sext (extract v_3 224 240) 18) (sext (extract v_4 224 240) 18));
      v_20 <- eval (sub (sext (extract v_3 240 256) 18) (sext (extract v_4 240 256) 18));
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_5 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_5 2 18))) (concat (mux (sgt v_6 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_6 2 18))) (concat (mux (sgt v_7 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_7 2 18))) (concat (mux (sgt v_8 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_8 2 18))) (concat (mux (sgt v_9 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_9 2 18))) (concat (mux (sgt v_10 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_10 2 18))) (concat (mux (sgt v_11 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_11 2 18))) (concat (mux (sgt v_12 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_12 2 18))) (concat (mux (sgt v_13 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_13 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_13 2 18))) (concat (mux (sgt v_14 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_14 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_14 2 18))) (concat (mux (sgt v_15 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_15 2 18))) (concat (mux (sgt v_16 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_16 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_16 2 18))) (concat (mux (sgt v_17 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_17 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_17 2 18))) (concat (mux (sgt v_18 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_18 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_18 2 18))) (concat (mux (sgt v_19 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_19 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_19 2 18))) (mux (sgt v_20 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_20 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) (extract v_20 2 18))))))))))))))))));
      pure ()
    pat_end

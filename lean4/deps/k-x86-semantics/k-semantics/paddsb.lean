def paddsb : instruction :=
  definst "paddsb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (add (sext (extract v_2 0 8) 16) (sext (extract v_4 0 8) 16));
      v_6 <- eval (add (sext (extract v_2 8 16) 16) (sext (extract v_4 8 16) 16));
      v_7 <- eval (add (sext (extract v_2 16 24) 16) (sext (extract v_4 16 24) 16));
      v_8 <- eval (add (sext (extract v_2 24 32) 16) (sext (extract v_4 24 32) 16));
      v_9 <- eval (add (sext (extract v_2 32 40) 16) (sext (extract v_4 32 40) 16));
      v_10 <- eval (add (sext (extract v_2 40 48) 16) (sext (extract v_4 40 48) 16));
      v_11 <- eval (add (sext (extract v_2 48 56) 16) (sext (extract v_4 48 56) 16));
      v_12 <- eval (add (sext (extract v_2 56 64) 16) (sext (extract v_4 56 64) 16));
      v_13 <- eval (add (sext (extract v_2 64 72) 16) (sext (extract v_4 64 72) 16));
      v_14 <- eval (add (sext (extract v_2 72 80) 16) (sext (extract v_4 72 80) 16));
      v_15 <- eval (add (sext (extract v_2 80 88) 16) (sext (extract v_4 80 88) 16));
      v_16 <- eval (add (sext (extract v_2 88 96) 16) (sext (extract v_4 88 96) 16));
      v_17 <- eval (add (sext (extract v_2 96 104) 16) (sext (extract v_4 96 104) 16));
      v_18 <- eval (add (sext (extract v_2 104 112) 16) (sext (extract v_4 104 112) 16));
      v_19 <- eval (add (sext (extract v_2 112 120) 16) (sext (extract v_4 112 120) 16));
      v_20 <- eval (add (sext (extract v_2 120 128) 16) (sext (extract v_4 120 128) 16));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_5 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5 8 16))) (concat (mux (sgt v_6 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_6 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_6 8 16))) (concat (mux (sgt v_7 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_7 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_7 8 16))) (concat (mux (sgt v_8 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_8 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_8 8 16))) (concat (mux (sgt v_9 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9 8 16))) (concat (mux (sgt v_10 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_10 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_10 8 16))) (concat (mux (sgt v_11 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_11 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_11 8 16))) (concat (mux (sgt v_12 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_12 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_12 8 16))) (concat (mux (sgt v_13 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_13 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_13 8 16))) (concat (mux (sgt v_14 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_14 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_14 8 16))) (concat (mux (sgt v_15 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_15 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_15 8 16))) (concat (mux (sgt v_16 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_16 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_16 8 16))) (concat (mux (sgt v_17 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_17 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_17 8 16))) (concat (mux (sgt v_18 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_18 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_18 8 16))) (concat (mux (sgt v_19 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_19 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_19 8 16))) (mux (sgt v_20 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_20 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_20 8 16))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (add (sext (extract v_2 0 8) 16) (sext (extract v_3 0 8) 16));
      v_5 <- eval (add (sext (extract v_2 8 16) 16) (sext (extract v_3 8 16) 16));
      v_6 <- eval (add (sext (extract v_2 16 24) 16) (sext (extract v_3 16 24) 16));
      v_7 <- eval (add (sext (extract v_2 24 32) 16) (sext (extract v_3 24 32) 16));
      v_8 <- eval (add (sext (extract v_2 32 40) 16) (sext (extract v_3 32 40) 16));
      v_9 <- eval (add (sext (extract v_2 40 48) 16) (sext (extract v_3 40 48) 16));
      v_10 <- eval (add (sext (extract v_2 48 56) 16) (sext (extract v_3 48 56) 16));
      v_11 <- eval (add (sext (extract v_2 56 64) 16) (sext (extract v_3 56 64) 16));
      v_12 <- eval (add (sext (extract v_2 64 72) 16) (sext (extract v_3 64 72) 16));
      v_13 <- eval (add (sext (extract v_2 72 80) 16) (sext (extract v_3 72 80) 16));
      v_14 <- eval (add (sext (extract v_2 80 88) 16) (sext (extract v_3 80 88) 16));
      v_15 <- eval (add (sext (extract v_2 88 96) 16) (sext (extract v_3 88 96) 16));
      v_16 <- eval (add (sext (extract v_2 96 104) 16) (sext (extract v_3 96 104) 16));
      v_17 <- eval (add (sext (extract v_2 104 112) 16) (sext (extract v_3 104 112) 16));
      v_18 <- eval (add (sext (extract v_2 112 120) 16) (sext (extract v_3 112 120) 16));
      v_19 <- eval (add (sext (extract v_2 120 128) 16) (sext (extract v_3 120 128) 16));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_4 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_4 8 16))) (concat (mux (sgt v_5 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5 8 16))) (concat (mux (sgt v_6 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_6 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_6 8 16))) (concat (mux (sgt v_7 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_7 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_7 8 16))) (concat (mux (sgt v_8 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_8 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_8 8 16))) (concat (mux (sgt v_9 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9 8 16))) (concat (mux (sgt v_10 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_10 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_10 8 16))) (concat (mux (sgt v_11 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_11 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_11 8 16))) (concat (mux (sgt v_12 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_12 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_12 8 16))) (concat (mux (sgt v_13 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_13 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_13 8 16))) (concat (mux (sgt v_14 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_14 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_14 8 16))) (concat (mux (sgt v_15 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_15 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_15 8 16))) (concat (mux (sgt v_16 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_16 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_16 8 16))) (concat (mux (sgt v_17 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_17 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_17 8 16))) (concat (mux (sgt v_18 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_18 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_18 8 16))) (mux (sgt v_19 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_19 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_19 8 16))))))))))))))))));
      pure ()
    pat_end

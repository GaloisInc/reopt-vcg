def psubsb1 : instruction :=
  definst "psubsb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (sub (sext (extract v_2 0 8) 10) (sext (extract v_4 0 8) 10));
      v_6 <- eval (sub (sext (extract v_2 8 16) 10) (sext (extract v_4 8 16) 10));
      v_7 <- eval (sub (sext (extract v_2 16 24) 10) (sext (extract v_4 16 24) 10));
      v_8 <- eval (sub (sext (extract v_2 24 32) 10) (sext (extract v_4 24 32) 10));
      v_9 <- eval (sub (sext (extract v_2 32 40) 10) (sext (extract v_4 32 40) 10));
      v_10 <- eval (sub (sext (extract v_2 40 48) 10) (sext (extract v_4 40 48) 10));
      v_11 <- eval (sub (sext (extract v_2 48 56) 10) (sext (extract v_4 48 56) 10));
      v_12 <- eval (sub (sext (extract v_2 56 64) 10) (sext (extract v_4 56 64) 10));
      v_13 <- eval (sub (sext (extract v_2 64 72) 10) (sext (extract v_4 64 72) 10));
      v_14 <- eval (sub (sext (extract v_2 72 80) 10) (sext (extract v_4 72 80) 10));
      v_15 <- eval (sub (sext (extract v_2 80 88) 10) (sext (extract v_4 80 88) 10));
      v_16 <- eval (sub (sext (extract v_2 88 96) 10) (sext (extract v_4 88 96) 10));
      v_17 <- eval (sub (sext (extract v_2 96 104) 10) (sext (extract v_4 96 104) 10));
      v_18 <- eval (sub (sext (extract v_2 104 112) 10) (sext (extract v_4 104 112) 10));
      v_19 <- eval (sub (sext (extract v_2 112 120) 10) (sext (extract v_4 112 120) 10));
      v_20 <- eval (sub (sext (extract v_2 120 128) 10) (sext (extract v_4 120 128) 10));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_5 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_5 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_5 2 10))) (concat (mux (sgt v_6 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_6 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_6 2 10))) (concat (mux (sgt v_7 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_7 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_7 2 10))) (concat (mux (sgt v_8 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8 2 10))) (concat (mux (sgt v_9 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_9 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_9 2 10))) (concat (mux (sgt v_10 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10 2 10))) (concat (mux (sgt v_11 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11 2 10))) (concat (mux (sgt v_12 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_12 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_12 2 10))) (concat (mux (sgt v_13 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_13 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_13 2 10))) (concat (mux (sgt v_14 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14 2 10))) (concat (mux (sgt v_15 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_15 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_15 2 10))) (concat (mux (sgt v_16 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_16 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_16 2 10))) (concat (mux (sgt v_17 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_17 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_17 2 10))) (concat (mux (sgt v_18 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_18 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_18 2 10))) (concat (mux (sgt v_19 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_19 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_19 2 10))) (mux (sgt v_20 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_20 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_20 2 10))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      v_4 <- eval (sub (sext (extract v_2 0 8) 10) (sext (extract v_3 0 8) 10));
      v_5 <- eval (sub (sext (extract v_2 8 16) 10) (sext (extract v_3 8 16) 10));
      v_6 <- eval (sub (sext (extract v_2 16 24) 10) (sext (extract v_3 16 24) 10));
      v_7 <- eval (sub (sext (extract v_2 24 32) 10) (sext (extract v_3 24 32) 10));
      v_8 <- eval (sub (sext (extract v_2 32 40) 10) (sext (extract v_3 32 40) 10));
      v_9 <- eval (sub (sext (extract v_2 40 48) 10) (sext (extract v_3 40 48) 10));
      v_10 <- eval (sub (sext (extract v_2 48 56) 10) (sext (extract v_3 48 56) 10));
      v_11 <- eval (sub (sext (extract v_2 56 64) 10) (sext (extract v_3 56 64) 10));
      v_12 <- eval (sub (sext (extract v_2 64 72) 10) (sext (extract v_3 64 72) 10));
      v_13 <- eval (sub (sext (extract v_2 72 80) 10) (sext (extract v_3 72 80) 10));
      v_14 <- eval (sub (sext (extract v_2 80 88) 10) (sext (extract v_3 80 88) 10));
      v_15 <- eval (sub (sext (extract v_2 88 96) 10) (sext (extract v_3 88 96) 10));
      v_16 <- eval (sub (sext (extract v_2 96 104) 10) (sext (extract v_3 96 104) 10));
      v_17 <- eval (sub (sext (extract v_2 104 112) 10) (sext (extract v_3 104 112) 10));
      v_18 <- eval (sub (sext (extract v_2 112 120) 10) (sext (extract v_3 112 120) 10));
      v_19 <- eval (sub (sext (extract v_2 120 128) 10) (sext (extract v_3 120 128) 10));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_4 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_4 2 10))) (concat (mux (sgt v_5 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_5 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_5 2 10))) (concat (mux (sgt v_6 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_6 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_6 2 10))) (concat (mux (sgt v_7 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_7 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_7 2 10))) (concat (mux (sgt v_8 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_8 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_8 2 10))) (concat (mux (sgt v_9 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_9 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_9 2 10))) (concat (mux (sgt v_10 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_10 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_10 2 10))) (concat (mux (sgt v_11 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_11 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_11 2 10))) (concat (mux (sgt v_12 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_12 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_12 2 10))) (concat (mux (sgt v_13 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_13 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_13 2 10))) (concat (mux (sgt v_14 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_14 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_14 2 10))) (concat (mux (sgt v_15 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_15 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_15 2 10))) (concat (mux (sgt v_16 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_16 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_16 2 10))) (concat (mux (sgt v_17 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_17 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_17 2 10))) (concat (mux (sgt v_18 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_18 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_18 2 10))) (mux (sgt v_19 (expression.bv_nat 10 127)) (expression.bv_nat 8 127) (mux (slt v_19 (expression.bv_nat 10 896)) (expression.bv_nat 8 128) (extract v_19 2 10))))))))))))))))));
      pure ()
    pat_end

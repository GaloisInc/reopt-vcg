def phsubsw1 : instruction :=
  definst "phsubsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (sub (sext (extract v_3 16 32) 32) (sext (extract v_3 0 16) 32));
      v_5 <- eval (sub (sext (extract v_3 48 64) 32) (sext (extract v_3 32 48) 32));
      v_6 <- eval (sub (sext (extract v_3 80 96) 32) (sext (extract v_3 64 80) 32));
      v_7 <- eval (sub (sext (extract v_3 112 128) 32) (sext (extract v_3 96 112) 32));
      v_8 <- getRegister xmm_1;
      v_9 <- eval (sub (sext (extract v_8 16 32) 32) (sext (extract v_8 0 16) 32));
      v_10 <- eval (sub (sext (extract v_8 48 64) 32) (sext (extract v_8 32 48) 32));
      v_11 <- eval (sub (sext (extract v_8 80 96) 32) (sext (extract v_8 64 80) 32));
      v_12 <- eval (sub (sext (extract v_8 112 128) 32) (sext (extract v_8 96 112) 32));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4 16 32))) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6 16 32))) (concat (mux (sgt v_7 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 16 32))) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10 16 32))) (concat (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11 16 32))) (mux (sgt v_12 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- eval (sub (sext (extract v_2 16 32) 32) (sext (extract v_2 0 16) 32));
      v_4 <- eval (sub (sext (extract v_2 48 64) 32) (sext (extract v_2 32 48) 32));
      v_5 <- eval (sub (sext (extract v_2 80 96) 32) (sext (extract v_2 64 80) 32));
      v_6 <- eval (sub (sext (extract v_2 112 128) 32) (sext (extract v_2 96 112) 32));
      v_7 <- getRegister xmm_1;
      v_8 <- eval (sub (sext (extract v_7 16 32) 32) (sext (extract v_7 0 16) 32));
      v_9 <- eval (sub (sext (extract v_7 48 64) 32) (sext (extract v_7 32 48) 32));
      v_10 <- eval (sub (sext (extract v_7 80 96) 32) (sext (extract v_7 64 80) 32));
      v_11 <- eval (sub (sext (extract v_7 112 128) 32) (sext (extract v_7 96 112) 32));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_3 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_3 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_3 16 32))) (concat (mux (sgt v_4 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4 16 32))) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6 16 32))) (concat (mux (sgt v_8 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 16 32))) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10 16 32))) (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11 16 32))))))))));
      pure ()
    pat_end

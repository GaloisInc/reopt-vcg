def paddsw : instruction :=
  definst "paddsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (add (sext (extract v_2 0 16) 32) (sext (extract v_4 0 16) 32));
      v_6 <- eval (add (sext (extract v_2 16 32) 32) (sext (extract v_4 16 32) 32));
      v_7 <- eval (add (sext (extract v_2 32 48) 32) (sext (extract v_4 32 48) 32));
      v_8 <- eval (add (sext (extract v_2 48 64) 32) (sext (extract v_4 48 64) 32));
      v_9 <- eval (add (sext (extract v_2 64 80) 32) (sext (extract v_4 64 80) 32));
      v_10 <- eval (add (sext (extract v_2 80 96) 32) (sext (extract v_4 80 96) 32));
      v_11 <- eval (add (sext (extract v_2 96 112) 32) (sext (extract v_4 96 112) 32));
      v_12 <- eval (add (sext (extract v_2 112 128) 32) (sext (extract v_4 112 128) 32));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6 16 32))) (concat (mux (sgt v_7 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 16 32))) (concat (mux (sgt v_8 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 16 32))) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10 16 32))) (concat (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11 16 32))) (mux (sgt v_12 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_12 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (add (sext (extract v_2 0 16) 32) (sext (extract v_3 0 16) 32));
      v_5 <- eval (add (sext (extract v_2 16 32) 32) (sext (extract v_3 16 32) 32));
      v_6 <- eval (add (sext (extract v_2 32 48) 32) (sext (extract v_3 32 48) 32));
      v_7 <- eval (add (sext (extract v_2 48 64) 32) (sext (extract v_3 48 64) 32));
      v_8 <- eval (add (sext (extract v_2 64 80) 32) (sext (extract v_3 64 80) 32));
      v_9 <- eval (add (sext (extract v_2 80 96) 32) (sext (extract v_3 80 96) 32));
      v_10 <- eval (add (sext (extract v_2 96 112) 32) (sext (extract v_3 96 112) 32));
      v_11 <- eval (add (sext (extract v_2 112 128) 32) (sext (extract v_3 112 128) 32));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4 16 32))) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5 16 32))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_6 16 32))) (concat (mux (sgt v_7 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 16 32))) (concat (mux (sgt v_8 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 16 32))) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_10 16 32))) (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11 16 32))))))))));
      pure ()
    pat_end

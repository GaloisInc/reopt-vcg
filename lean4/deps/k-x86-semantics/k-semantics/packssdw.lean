def packssdw1 : instruction :=
  definst "packssdw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (extract v_3 0 32);
      v_5 <- eval (extract v_3 32 64);
      v_6 <- eval (extract v_3 64 96);
      v_7 <- eval (extract v_3 96 128);
      v_8 <- getRegister xmm_1;
      v_9 <- eval (extract v_8 0 32);
      v_10 <- eval (extract v_8 32 64);
      v_11 <- eval (extract v_8 64 96);
      v_12 <- eval (extract v_8 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_3 16 32))) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_3 48 64))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_3 80 96))) (concat (mux (sgt v_7 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_3 112 128))) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 16 32))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 48 64))) (concat (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 80 96))) (mux (sgt v_12 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_8 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- eval (extract v_2 0 32);
      v_4 <- eval (extract v_2 32 64);
      v_5 <- eval (extract v_2 64 96);
      v_6 <- eval (extract v_2 96 128);
      v_7 <- getRegister xmm_1;
      v_8 <- eval (extract v_7 0 32);
      v_9 <- eval (extract v_7 32 64);
      v_10 <- eval (extract v_7 64 96);
      v_11 <- eval (extract v_7 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_3 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_3 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_2 16 32))) (concat (mux (sgt v_4 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_2 48 64))) (concat (mux (sgt v_5 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_2 80 96))) (concat (mux (sgt v_6 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_6 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_2 112 128))) (concat (mux (sgt v_8 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 16 32))) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 48 64))) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 80 96))) (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_7 112 128))))))))));
      pure ()
    pat_end

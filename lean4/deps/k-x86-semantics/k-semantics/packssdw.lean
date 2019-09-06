def packssdw1 : instruction :=
  definst "packssdw" $ do
    pattern fun (v_3163 : reg (bv 128)) (v_3164 : reg (bv 128)) => do
      v_5285 <- getRegister v_3163;
      v_5286 <- eval (extract v_5285 0 32);
      v_5292 <- eval (extract v_5285 32 64);
      v_5298 <- eval (extract v_5285 64 96);
      v_5304 <- eval (extract v_5285 96 128);
      v_5310 <- getRegister v_3164;
      v_5311 <- eval (extract v_5310 0 32);
      v_5317 <- eval (extract v_5310 32 64);
      v_5323 <- eval (extract v_5310 64 96);
      v_5329 <- eval (extract v_5310 96 128);
      setRegister (lhs.of_reg v_3164) (concat (mux (sgt v_5286 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5286 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5285 16 32))) (concat (mux (sgt v_5292 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5292 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5285 48 64))) (concat (mux (sgt v_5298 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5298 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5285 80 96))) (concat (mux (sgt v_5304 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5304 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5285 112 128))) (concat (mux (sgt v_5311 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5311 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5310 16 32))) (concat (mux (sgt v_5317 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5317 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5310 48 64))) (concat (mux (sgt v_5323 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5323 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5310 80 96))) (mux (sgt v_5329 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5329 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5310 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3159 : Mem) (v_3160 : reg (bv 128)) => do
      v_9232 <- evaluateAddress v_3159;
      v_9233 <- load v_9232 16;
      v_9234 <- eval (extract v_9233 0 32);
      v_9240 <- eval (extract v_9233 32 64);
      v_9246 <- eval (extract v_9233 64 96);
      v_9252 <- eval (extract v_9233 96 128);
      v_9258 <- getRegister v_3160;
      v_9259 <- eval (extract v_9258 0 32);
      v_9265 <- eval (extract v_9258 32 64);
      v_9271 <- eval (extract v_9258 64 96);
      v_9277 <- eval (extract v_9258 96 128);
      setRegister (lhs.of_reg v_3160) (concat (mux (sgt v_9234 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9234 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9233 16 32))) (concat (mux (sgt v_9240 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9240 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9233 48 64))) (concat (mux (sgt v_9246 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9246 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9233 80 96))) (concat (mux (sgt v_9252 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9252 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9233 112 128))) (concat (mux (sgt v_9259 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9259 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9258 16 32))) (concat (mux (sgt v_9265 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9265 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9258 48 64))) (concat (mux (sgt v_9271 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9271 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9258 80 96))) (mux (sgt v_9277 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9277 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9258 112 128))))))))));
      pure ()
    pat_end

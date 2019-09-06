def phsubsw1 : instruction :=
  definst "phsubsw" $ do
    pattern fun (v_2564 : reg (bv 128)) (v_2565 : reg (bv 128)) => do
      v_4332 <- getRegister v_2564;
      v_4337 <- eval (sub (sext (extract v_4332 16 32) 32) (sext (extract v_4332 0 16) 32));
      v_4347 <- eval (sub (sext (extract v_4332 48 64) 32) (sext (extract v_4332 32 48) 32));
      v_4357 <- eval (sub (sext (extract v_4332 80 96) 32) (sext (extract v_4332 64 80) 32));
      v_4367 <- eval (sub (sext (extract v_4332 112 128) 32) (sext (extract v_4332 96 112) 32));
      v_4373 <- getRegister v_2565;
      v_4378 <- eval (sub (sext (extract v_4373 16 32) 32) (sext (extract v_4373 0 16) 32));
      v_4388 <- eval (sub (sext (extract v_4373 48 64) 32) (sext (extract v_4373 32 48) 32));
      v_4398 <- eval (sub (sext (extract v_4373 80 96) 32) (sext (extract v_4373 64 80) 32));
      v_4408 <- eval (sub (sext (extract v_4373 112 128) 32) (sext (extract v_4373 96 112) 32));
      setRegister (lhs.of_reg v_2565) (concat (mux (sgt v_4337 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4337 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4337 16 32))) (concat (mux (sgt v_4347 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4347 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4347 16 32))) (concat (mux (sgt v_4357 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4357 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4357 16 32))) (concat (mux (sgt v_4367 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4367 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4367 16 32))) (concat (mux (sgt v_4378 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4378 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4378 16 32))) (concat (mux (sgt v_4388 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4388 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4388 16 32))) (concat (mux (sgt v_4398 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4398 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4398 16 32))) (mux (sgt v_4408 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4408 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4408 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2560 : Mem) (v_2561 : reg (bv 128)) => do
      v_11226 <- evaluateAddress v_2560;
      v_11227 <- load v_11226 16;
      v_11232 <- eval (sub (sext (extract v_11227 16 32) 32) (sext (extract v_11227 0 16) 32));
      v_11242 <- eval (sub (sext (extract v_11227 48 64) 32) (sext (extract v_11227 32 48) 32));
      v_11252 <- eval (sub (sext (extract v_11227 80 96) 32) (sext (extract v_11227 64 80) 32));
      v_11262 <- eval (sub (sext (extract v_11227 112 128) 32) (sext (extract v_11227 96 112) 32));
      v_11268 <- getRegister v_2561;
      v_11273 <- eval (sub (sext (extract v_11268 16 32) 32) (sext (extract v_11268 0 16) 32));
      v_11283 <- eval (sub (sext (extract v_11268 48 64) 32) (sext (extract v_11268 32 48) 32));
      v_11293 <- eval (sub (sext (extract v_11268 80 96) 32) (sext (extract v_11268 64 80) 32));
      v_11303 <- eval (sub (sext (extract v_11268 112 128) 32) (sext (extract v_11268 96 112) 32));
      setRegister (lhs.of_reg v_2561) (concat (mux (sgt v_11232 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11232 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11232 16 32))) (concat (mux (sgt v_11242 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11242 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11242 16 32))) (concat (mux (sgt v_11252 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11252 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11252 16 32))) (concat (mux (sgt v_11262 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11262 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11262 16 32))) (concat (mux (sgt v_11273 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11273 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11273 16 32))) (concat (mux (sgt v_11283 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11283 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11283 16 32))) (concat (mux (sgt v_11293 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11293 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11293 16 32))) (mux (sgt v_11303 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11303 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11303 16 32))))))))));
      pure ()
    pat_end

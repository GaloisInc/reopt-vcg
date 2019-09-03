def phsubsw1 : instruction :=
  definst "phsubsw" $ do
    pattern fun (v_2487 : reg (bv 128)) (v_2488 : reg (bv 128)) => do
      v_4254 <- getRegister v_2487;
      v_4259 <- eval (sub (leanSignExtend (extract v_4254 16 32) 32) (leanSignExtend (extract v_4254 0 16) 32));
      v_4269 <- eval (sub (leanSignExtend (extract v_4254 48 64) 32) (leanSignExtend (extract v_4254 32 48) 32));
      v_4279 <- eval (sub (leanSignExtend (extract v_4254 80 96) 32) (leanSignExtend (extract v_4254 64 80) 32));
      v_4289 <- eval (sub (leanSignExtend (extract v_4254 112 128) 32) (leanSignExtend (extract v_4254 96 112) 32));
      v_4295 <- getRegister v_2488;
      v_4300 <- eval (sub (leanSignExtend (extract v_4295 16 32) 32) (leanSignExtend (extract v_4295 0 16) 32));
      v_4310 <- eval (sub (leanSignExtend (extract v_4295 48 64) 32) (leanSignExtend (extract v_4295 32 48) 32));
      v_4320 <- eval (sub (leanSignExtend (extract v_4295 80 96) 32) (leanSignExtend (extract v_4295 64 80) 32));
      v_4330 <- eval (sub (leanSignExtend (extract v_4295 112 128) 32) (leanSignExtend (extract v_4295 96 112) 32));
      setRegister (lhs.of_reg v_2488) (concat (mux (sgt v_4259 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4259 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4259 16 32))) (concat (mux (sgt v_4269 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4269 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4269 16 32))) (concat (mux (sgt v_4279 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4279 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4279 16 32))) (concat (mux (sgt v_4289 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4289 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4289 16 32))) (concat (mux (sgt v_4300 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4300 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4300 16 32))) (concat (mux (sgt v_4310 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4310 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4310 16 32))) (concat (mux (sgt v_4320 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4320 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4320 16 32))) (mux (sgt v_4330 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4330 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4330 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2483 : Mem) (v_2484 : reg (bv 128)) => do
      v_11373 <- evaluateAddress v_2483;
      v_11374 <- load v_11373 16;
      v_11379 <- eval (sub (leanSignExtend (extract v_11374 16 32) 32) (leanSignExtend (extract v_11374 0 16) 32));
      v_11389 <- eval (sub (leanSignExtend (extract v_11374 48 64) 32) (leanSignExtend (extract v_11374 32 48) 32));
      v_11399 <- eval (sub (leanSignExtend (extract v_11374 80 96) 32) (leanSignExtend (extract v_11374 64 80) 32));
      v_11409 <- eval (sub (leanSignExtend (extract v_11374 112 128) 32) (leanSignExtend (extract v_11374 96 112) 32));
      v_11415 <- getRegister v_2484;
      v_11420 <- eval (sub (leanSignExtend (extract v_11415 16 32) 32) (leanSignExtend (extract v_11415 0 16) 32));
      v_11430 <- eval (sub (leanSignExtend (extract v_11415 48 64) 32) (leanSignExtend (extract v_11415 32 48) 32));
      v_11440 <- eval (sub (leanSignExtend (extract v_11415 80 96) 32) (leanSignExtend (extract v_11415 64 80) 32));
      v_11450 <- eval (sub (leanSignExtend (extract v_11415 112 128) 32) (leanSignExtend (extract v_11415 96 112) 32));
      setRegister (lhs.of_reg v_2484) (concat (mux (sgt v_11379 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11379 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11379 16 32))) (concat (mux (sgt v_11389 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11389 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11389 16 32))) (concat (mux (sgt v_11399 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11399 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11399 16 32))) (concat (mux (sgt v_11409 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11409 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11409 16 32))) (concat (mux (sgt v_11420 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11420 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11420 16 32))) (concat (mux (sgt v_11430 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11430 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11430 16 32))) (concat (mux (sgt v_11440 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11440 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11440 16 32))) (mux (sgt v_11450 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11450 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11450 16 32))))))))));
      pure ()
    pat_end

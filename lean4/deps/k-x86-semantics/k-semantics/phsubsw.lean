def phsubsw1 : instruction :=
  definst "phsubsw" $ do
    pattern fun (v_2536 : reg (bv 128)) (v_2537 : reg (bv 128)) => do
      v_4305 <- getRegister v_2536;
      v_4310 <- eval (sub (sext (extract v_4305 16 32) 32) (sext (extract v_4305 0 16) 32));
      v_4320 <- eval (sub (sext (extract v_4305 48 64) 32) (sext (extract v_4305 32 48) 32));
      v_4330 <- eval (sub (sext (extract v_4305 80 96) 32) (sext (extract v_4305 64 80) 32));
      v_4340 <- eval (sub (sext (extract v_4305 112 128) 32) (sext (extract v_4305 96 112) 32));
      v_4346 <- getRegister v_2537;
      v_4351 <- eval (sub (sext (extract v_4346 16 32) 32) (sext (extract v_4346 0 16) 32));
      v_4361 <- eval (sub (sext (extract v_4346 48 64) 32) (sext (extract v_4346 32 48) 32));
      v_4371 <- eval (sub (sext (extract v_4346 80 96) 32) (sext (extract v_4346 64 80) 32));
      v_4381 <- eval (sub (sext (extract v_4346 112 128) 32) (sext (extract v_4346 96 112) 32));
      setRegister (lhs.of_reg v_2537) (concat (mux (sgt v_4310 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4310 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4310 16 32))) (concat (mux (sgt v_4320 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4320 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4320 16 32))) (concat (mux (sgt v_4330 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4330 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4330 16 32))) (concat (mux (sgt v_4340 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4340 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4340 16 32))) (concat (mux (sgt v_4351 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4351 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4351 16 32))) (concat (mux (sgt v_4361 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4361 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4361 16 32))) (concat (mux (sgt v_4371 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4371 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4371 16 32))) (mux (sgt v_4381 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4381 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4381 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2533 : Mem) (v_2532 : reg (bv 128)) => do
      v_11250 <- evaluateAddress v_2533;
      v_11251 <- load v_11250 16;
      v_11256 <- eval (sub (sext (extract v_11251 16 32) 32) (sext (extract v_11251 0 16) 32));
      v_11266 <- eval (sub (sext (extract v_11251 48 64) 32) (sext (extract v_11251 32 48) 32));
      v_11276 <- eval (sub (sext (extract v_11251 80 96) 32) (sext (extract v_11251 64 80) 32));
      v_11286 <- eval (sub (sext (extract v_11251 112 128) 32) (sext (extract v_11251 96 112) 32));
      v_11292 <- getRegister v_2532;
      v_11297 <- eval (sub (sext (extract v_11292 16 32) 32) (sext (extract v_11292 0 16) 32));
      v_11307 <- eval (sub (sext (extract v_11292 48 64) 32) (sext (extract v_11292 32 48) 32));
      v_11317 <- eval (sub (sext (extract v_11292 80 96) 32) (sext (extract v_11292 64 80) 32));
      v_11327 <- eval (sub (sext (extract v_11292 112 128) 32) (sext (extract v_11292 96 112) 32));
      setRegister (lhs.of_reg v_2532) (concat (mux (sgt v_11256 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11256 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11256 16 32))) (concat (mux (sgt v_11266 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11266 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11266 16 32))) (concat (mux (sgt v_11276 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11276 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11276 16 32))) (concat (mux (sgt v_11286 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11286 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11286 16 32))) (concat (mux (sgt v_11297 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11297 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11297 16 32))) (concat (mux (sgt v_11307 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11307 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11307 16 32))) (concat (mux (sgt v_11317 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11317 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11317 16 32))) (mux (sgt v_11327 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11327 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_11327 16 32))))))))));
      pure ()
    pat_end

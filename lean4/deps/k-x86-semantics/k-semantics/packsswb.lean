def packsswb1 : instruction :=
  definst "packsswb" $ do
    pattern fun (v_3172 : reg (bv 128)) (v_3173 : reg (bv 128)) => do
      v_5347 <- getRegister v_3172;
      v_5348 <- eval (extract v_5347 0 16);
      v_5354 <- eval (extract v_5347 16 32);
      v_5360 <- eval (extract v_5347 32 48);
      v_5366 <- eval (extract v_5347 48 64);
      v_5372 <- eval (extract v_5347 64 80);
      v_5378 <- eval (extract v_5347 80 96);
      v_5384 <- eval (extract v_5347 96 112);
      v_5390 <- eval (extract v_5347 112 128);
      v_5396 <- getRegister v_3173;
      v_5397 <- eval (extract v_5396 0 16);
      v_5403 <- eval (extract v_5396 16 32);
      v_5409 <- eval (extract v_5396 32 48);
      v_5415 <- eval (extract v_5396 48 64);
      v_5421 <- eval (extract v_5396 64 80);
      v_5427 <- eval (extract v_5396 80 96);
      v_5433 <- eval (extract v_5396 96 112);
      v_5439 <- eval (extract v_5396 112 128);
      setRegister (lhs.of_reg v_3173) (concat (mux (sgt v_5348 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5348 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5347 8 16))) (concat (mux (sgt v_5354 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5354 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5347 24 32))) (concat (mux (sgt v_5360 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5360 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5347 40 48))) (concat (mux (sgt v_5366 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5366 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5347 56 64))) (concat (mux (sgt v_5372 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5372 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5347 72 80))) (concat (mux (sgt v_5378 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5378 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5347 88 96))) (concat (mux (sgt v_5384 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5384 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5347 104 112))) (concat (mux (sgt v_5390 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5390 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5347 120 128))) (concat (mux (sgt v_5397 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5397 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5396 8 16))) (concat (mux (sgt v_5403 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5403 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5396 24 32))) (concat (mux (sgt v_5409 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5409 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5396 40 48))) (concat (mux (sgt v_5415 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5415 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5396 56 64))) (concat (mux (sgt v_5421 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5421 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5396 72 80))) (concat (mux (sgt v_5427 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5427 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5396 88 96))) (concat (mux (sgt v_5433 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5433 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5396 104 112))) (mux (sgt v_5439 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5439 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5396 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3168 : Mem) (v_3169 : reg (bv 128)) => do
      v_9291 <- evaluateAddress v_3168;
      v_9292 <- load v_9291 16;
      v_9293 <- eval (extract v_9292 0 16);
      v_9299 <- eval (extract v_9292 16 32);
      v_9305 <- eval (extract v_9292 32 48);
      v_9311 <- eval (extract v_9292 48 64);
      v_9317 <- eval (extract v_9292 64 80);
      v_9323 <- eval (extract v_9292 80 96);
      v_9329 <- eval (extract v_9292 96 112);
      v_9335 <- eval (extract v_9292 112 128);
      v_9341 <- getRegister v_3169;
      v_9342 <- eval (extract v_9341 0 16);
      v_9348 <- eval (extract v_9341 16 32);
      v_9354 <- eval (extract v_9341 32 48);
      v_9360 <- eval (extract v_9341 48 64);
      v_9366 <- eval (extract v_9341 64 80);
      v_9372 <- eval (extract v_9341 80 96);
      v_9378 <- eval (extract v_9341 96 112);
      v_9384 <- eval (extract v_9341 112 128);
      setRegister (lhs.of_reg v_3169) (concat (mux (sgt v_9293 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9293 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9292 8 16))) (concat (mux (sgt v_9299 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9299 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9292 24 32))) (concat (mux (sgt v_9305 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9305 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9292 40 48))) (concat (mux (sgt v_9311 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9311 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9292 56 64))) (concat (mux (sgt v_9317 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9317 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9292 72 80))) (concat (mux (sgt v_9323 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9323 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9292 88 96))) (concat (mux (sgt v_9329 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9329 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9292 104 112))) (concat (mux (sgt v_9335 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9335 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9292 120 128))) (concat (mux (sgt v_9342 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9342 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9341 8 16))) (concat (mux (sgt v_9348 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9348 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9341 24 32))) (concat (mux (sgt v_9354 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9354 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9341 40 48))) (concat (mux (sgt v_9360 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9360 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9341 56 64))) (concat (mux (sgt v_9366 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9366 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9341 72 80))) (concat (mux (sgt v_9372 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9372 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9341 88 96))) (concat (mux (sgt v_9378 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9378 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9341 104 112))) (mux (sgt v_9384 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9384 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9341 120 128))))))))))))))))));
      pure ()
    pat_end

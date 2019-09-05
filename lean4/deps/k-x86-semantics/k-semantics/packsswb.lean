def packsswb1 : instruction :=
  definst "packsswb" $ do
    pattern fun (v_3147 : reg (bv 128)) (v_3148 : reg (bv 128)) => do
      v_5320 <- getRegister v_3147;
      v_5321 <- eval (extract v_5320 0 16);
      v_5327 <- eval (extract v_5320 16 32);
      v_5333 <- eval (extract v_5320 32 48);
      v_5339 <- eval (extract v_5320 48 64);
      v_5345 <- eval (extract v_5320 64 80);
      v_5351 <- eval (extract v_5320 80 96);
      v_5357 <- eval (extract v_5320 96 112);
      v_5363 <- eval (extract v_5320 112 128);
      v_5369 <- getRegister v_3148;
      v_5370 <- eval (extract v_5369 0 16);
      v_5376 <- eval (extract v_5369 16 32);
      v_5382 <- eval (extract v_5369 32 48);
      v_5388 <- eval (extract v_5369 48 64);
      v_5394 <- eval (extract v_5369 64 80);
      v_5400 <- eval (extract v_5369 80 96);
      v_5406 <- eval (extract v_5369 96 112);
      v_5412 <- eval (extract v_5369 112 128);
      setRegister (lhs.of_reg v_3148) (concat (mux (sgt v_5321 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5321 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5320 8 16))) (concat (mux (sgt v_5327 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5327 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5320 24 32))) (concat (mux (sgt v_5333 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5333 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5320 40 48))) (concat (mux (sgt v_5339 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5339 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5320 56 64))) (concat (mux (sgt v_5345 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5345 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5320 72 80))) (concat (mux (sgt v_5351 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5351 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5320 88 96))) (concat (mux (sgt v_5357 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5357 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5320 104 112))) (concat (mux (sgt v_5363 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5363 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5320 120 128))) (concat (mux (sgt v_5370 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5370 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5369 8 16))) (concat (mux (sgt v_5376 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5376 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5369 24 32))) (concat (mux (sgt v_5382 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5382 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5369 40 48))) (concat (mux (sgt v_5388 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5388 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5369 56 64))) (concat (mux (sgt v_5394 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5394 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5369 72 80))) (concat (mux (sgt v_5400 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5400 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5369 88 96))) (concat (mux (sgt v_5406 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5406 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5369 104 112))) (mux (sgt v_5412 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_5412 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_5369 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3142 : Mem) (v_3143 : reg (bv 128)) => do
      v_9264 <- evaluateAddress v_3142;
      v_9265 <- load v_9264 16;
      v_9266 <- eval (extract v_9265 0 16);
      v_9272 <- eval (extract v_9265 16 32);
      v_9278 <- eval (extract v_9265 32 48);
      v_9284 <- eval (extract v_9265 48 64);
      v_9290 <- eval (extract v_9265 64 80);
      v_9296 <- eval (extract v_9265 80 96);
      v_9302 <- eval (extract v_9265 96 112);
      v_9308 <- eval (extract v_9265 112 128);
      v_9314 <- getRegister v_3143;
      v_9315 <- eval (extract v_9314 0 16);
      v_9321 <- eval (extract v_9314 16 32);
      v_9327 <- eval (extract v_9314 32 48);
      v_9333 <- eval (extract v_9314 48 64);
      v_9339 <- eval (extract v_9314 64 80);
      v_9345 <- eval (extract v_9314 80 96);
      v_9351 <- eval (extract v_9314 96 112);
      v_9357 <- eval (extract v_9314 112 128);
      setRegister (lhs.of_reg v_3143) (concat (mux (sgt v_9266 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9266 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9265 8 16))) (concat (mux (sgt v_9272 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9272 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9265 24 32))) (concat (mux (sgt v_9278 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9278 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9265 40 48))) (concat (mux (sgt v_9284 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9284 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9265 56 64))) (concat (mux (sgt v_9290 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9290 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9265 72 80))) (concat (mux (sgt v_9296 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9296 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9265 88 96))) (concat (mux (sgt v_9302 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9302 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9265 104 112))) (concat (mux (sgt v_9308 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9308 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9265 120 128))) (concat (mux (sgt v_9315 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9315 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9314 8 16))) (concat (mux (sgt v_9321 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9321 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9314 24 32))) (concat (mux (sgt v_9327 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9327 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9314 40 48))) (concat (mux (sgt v_9333 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9333 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9314 56 64))) (concat (mux (sgt v_9339 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9339 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9314 72 80))) (concat (mux (sgt v_9345 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9345 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9314 88 96))) (concat (mux (sgt v_9351 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9351 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9314 104 112))) (mux (sgt v_9357 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_9357 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) (extract v_9314 120 128))))))))))))))))));
      pure ()
    pat_end

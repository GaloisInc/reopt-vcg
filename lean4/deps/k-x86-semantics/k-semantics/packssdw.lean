def packssdw1 : instruction :=
  definst "packssdw" $ do
    pattern fun (v_3087 : reg (bv 128)) (v_3088 : reg (bv 128)) => do
      v_5345 <- getRegister v_3087;
      v_5346 <- eval (extract v_5345 0 32);
      v_5352 <- eval (extract v_5345 32 64);
      v_5358 <- eval (extract v_5345 64 96);
      v_5364 <- eval (extract v_5345 96 128);
      v_5370 <- getRegister v_3088;
      v_5371 <- eval (extract v_5370 0 32);
      v_5377 <- eval (extract v_5370 32 64);
      v_5383 <- eval (extract v_5370 64 96);
      v_5389 <- eval (extract v_5370 96 128);
      setRegister (lhs.of_reg v_3088) (concat (mux (sgt v_5346 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5346 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5345 16 32))) (concat (mux (sgt v_5352 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5352 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5345 48 64))) (concat (mux (sgt v_5358 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5358 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5345 80 96))) (concat (mux (sgt v_5364 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5364 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5345 112 128))) (concat (mux (sgt v_5371 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5371 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5370 16 32))) (concat (mux (sgt v_5377 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5377 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5370 48 64))) (concat (mux (sgt v_5383 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5383 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5370 80 96))) (mux (sgt v_5389 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_5389 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_5370 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3083 : Mem) (v_3084 : reg (bv 128)) => do
      v_9441 <- evaluateAddress v_3083;
      v_9442 <- load v_9441 16;
      v_9443 <- eval (extract v_9442 0 32);
      v_9449 <- eval (extract v_9442 32 64);
      v_9455 <- eval (extract v_9442 64 96);
      v_9461 <- eval (extract v_9442 96 128);
      v_9467 <- getRegister v_3084;
      v_9468 <- eval (extract v_9467 0 32);
      v_9474 <- eval (extract v_9467 32 64);
      v_9480 <- eval (extract v_9467 64 96);
      v_9486 <- eval (extract v_9467 96 128);
      setRegister (lhs.of_reg v_3084) (concat (mux (sgt v_9443 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9443 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9442 16 32))) (concat (mux (sgt v_9449 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9449 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9442 48 64))) (concat (mux (sgt v_9455 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9455 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9442 80 96))) (concat (mux (sgt v_9461 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9461 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9442 112 128))) (concat (mux (sgt v_9468 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9468 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9467 16 32))) (concat (mux (sgt v_9474 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9474 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9467 48 64))) (concat (mux (sgt v_9480 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9480 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9467 80 96))) (mux (sgt v_9486 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9486 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_9467 112 128))))))))));
      pure ()
    pat_end

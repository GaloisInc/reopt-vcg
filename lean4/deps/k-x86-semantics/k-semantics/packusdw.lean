def packusdw1 : instruction :=
  definst "packusdw" $ do
    pattern fun (v_3156 : reg (bv 128)) (v_3157 : reg (bv 128)) => do
      v_5438 <- getRegister v_3156;
      v_5439 <- eval (extract v_5438 0 32);
      v_5445 <- eval (extract v_5438 32 64);
      v_5451 <- eval (extract v_5438 64 96);
      v_5457 <- eval (extract v_5438 96 128);
      v_5463 <- getRegister v_3157;
      v_5464 <- eval (extract v_5463 0 32);
      v_5470 <- eval (extract v_5463 32 64);
      v_5476 <- eval (extract v_5463 64 96);
      v_5482 <- eval (extract v_5463 96 128);
      setRegister (lhs.of_reg v_3157) (concat (mux (sgt v_5439 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5439 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5438 16 32))) (concat (mux (sgt v_5445 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5445 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5438 48 64))) (concat (mux (sgt v_5451 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5451 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5438 80 96))) (concat (mux (sgt v_5457 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5457 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5438 112 128))) (concat (mux (sgt v_5464 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5464 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5463 16 32))) (concat (mux (sgt v_5470 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5470 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5463 48 64))) (concat (mux (sgt v_5476 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5476 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5463 80 96))) (mux (sgt v_5482 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5482 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5463 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3151 : Mem) (v_3152 : reg (bv 128)) => do
      v_9379 <- evaluateAddress v_3151;
      v_9380 <- load v_9379 16;
      v_9381 <- eval (extract v_9380 0 32);
      v_9387 <- eval (extract v_9380 32 64);
      v_9393 <- eval (extract v_9380 64 96);
      v_9399 <- eval (extract v_9380 96 128);
      v_9405 <- getRegister v_3152;
      v_9406 <- eval (extract v_9405 0 32);
      v_9412 <- eval (extract v_9405 32 64);
      v_9418 <- eval (extract v_9405 64 96);
      v_9424 <- eval (extract v_9405 96 128);
      setRegister (lhs.of_reg v_3152) (concat (mux (sgt v_9381 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9381 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9380 16 32))) (concat (mux (sgt v_9387 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9387 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9380 48 64))) (concat (mux (sgt v_9393 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9393 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9380 80 96))) (concat (mux (sgt v_9399 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9399 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9380 112 128))) (concat (mux (sgt v_9406 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9406 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9405 16 32))) (concat (mux (sgt v_9412 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9412 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9405 48 64))) (concat (mux (sgt v_9418 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9418 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9405 80 96))) (mux (sgt v_9424 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9424 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9405 112 128))))))))));
      pure ()
    pat_end

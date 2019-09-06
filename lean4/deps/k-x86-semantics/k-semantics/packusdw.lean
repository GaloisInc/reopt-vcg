def packusdw1 : instruction :=
  definst "packusdw" $ do
    pattern fun (v_3181 : reg (bv 128)) (v_3182 : reg (bv 128)) => do
      v_5465 <- getRegister v_3181;
      v_5466 <- eval (extract v_5465 0 32);
      v_5472 <- eval (extract v_5465 32 64);
      v_5478 <- eval (extract v_5465 64 96);
      v_5484 <- eval (extract v_5465 96 128);
      v_5490 <- getRegister v_3182;
      v_5491 <- eval (extract v_5490 0 32);
      v_5497 <- eval (extract v_5490 32 64);
      v_5503 <- eval (extract v_5490 64 96);
      v_5509 <- eval (extract v_5490 96 128);
      setRegister (lhs.of_reg v_3182) (concat (mux (sgt v_5466 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5466 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5465 16 32))) (concat (mux (sgt v_5472 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5472 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5465 48 64))) (concat (mux (sgt v_5478 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5478 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5465 80 96))) (concat (mux (sgt v_5484 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5484 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5465 112 128))) (concat (mux (sgt v_5491 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5491 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5490 16 32))) (concat (mux (sgt v_5497 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5497 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5490 48 64))) (concat (mux (sgt v_5503 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5503 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5490 80 96))) (mux (sgt v_5509 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5509 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5490 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3177 : Mem) (v_3178 : reg (bv 128)) => do
      v_9406 <- evaluateAddress v_3177;
      v_9407 <- load v_9406 16;
      v_9408 <- eval (extract v_9407 0 32);
      v_9414 <- eval (extract v_9407 32 64);
      v_9420 <- eval (extract v_9407 64 96);
      v_9426 <- eval (extract v_9407 96 128);
      v_9432 <- getRegister v_3178;
      v_9433 <- eval (extract v_9432 0 32);
      v_9439 <- eval (extract v_9432 32 64);
      v_9445 <- eval (extract v_9432 64 96);
      v_9451 <- eval (extract v_9432 96 128);
      setRegister (lhs.of_reg v_3178) (concat (mux (sgt v_9408 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9408 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9407 16 32))) (concat (mux (sgt v_9414 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9414 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9407 48 64))) (concat (mux (sgt v_9420 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9420 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9407 80 96))) (concat (mux (sgt v_9426 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9426 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9407 112 128))) (concat (mux (sgt v_9433 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9433 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9432 16 32))) (concat (mux (sgt v_9439 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9439 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9432 48 64))) (concat (mux (sgt v_9445 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9445 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9432 80 96))) (mux (sgt v_9451 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9451 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9432 112 128))))))))));
      pure ()
    pat_end

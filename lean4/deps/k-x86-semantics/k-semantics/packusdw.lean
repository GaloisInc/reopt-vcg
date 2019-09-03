def packusdw1 : instruction :=
  definst "packusdw" $ do
    pattern fun (v_3105 : reg (bv 128)) (v_3106 : reg (bv 128)) => do
      v_5525 <- getRegister v_3105;
      v_5526 <- eval (extract v_5525 0 32);
      v_5532 <- eval (extract v_5525 32 64);
      v_5538 <- eval (extract v_5525 64 96);
      v_5544 <- eval (extract v_5525 96 128);
      v_5550 <- getRegister v_3106;
      v_5551 <- eval (extract v_5550 0 32);
      v_5557 <- eval (extract v_5550 32 64);
      v_5563 <- eval (extract v_5550 64 96);
      v_5569 <- eval (extract v_5550 96 128);
      setRegister (lhs.of_reg v_3106) (concat (mux (sgt v_5526 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5526 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5525 16 32))) (concat (mux (sgt v_5532 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5532 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5525 48 64))) (concat (mux (sgt v_5538 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5538 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5525 80 96))) (concat (mux (sgt v_5544 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5544 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5525 112 128))) (concat (mux (sgt v_5551 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5551 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5550 16 32))) (concat (mux (sgt v_5557 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5557 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5550 48 64))) (concat (mux (sgt v_5563 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5563 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5550 80 96))) (mux (sgt v_5569 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5569 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5550 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3101 : Mem) (v_3102 : reg (bv 128)) => do
      v_9615 <- evaluateAddress v_3101;
      v_9616 <- load v_9615 16;
      v_9617 <- eval (extract v_9616 0 32);
      v_9623 <- eval (extract v_9616 32 64);
      v_9629 <- eval (extract v_9616 64 96);
      v_9635 <- eval (extract v_9616 96 128);
      v_9641 <- getRegister v_3102;
      v_9642 <- eval (extract v_9641 0 32);
      v_9648 <- eval (extract v_9641 32 64);
      v_9654 <- eval (extract v_9641 64 96);
      v_9660 <- eval (extract v_9641 96 128);
      setRegister (lhs.of_reg v_3102) (concat (mux (sgt v_9617 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9617 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9616 16 32))) (concat (mux (sgt v_9623 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9623 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9616 48 64))) (concat (mux (sgt v_9629 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9629 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9616 80 96))) (concat (mux (sgt v_9635 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9635 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9616 112 128))) (concat (mux (sgt v_9642 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9642 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9641 16 32))) (concat (mux (sgt v_9648 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9648 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9641 48 64))) (concat (mux (sgt v_9654 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9654 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9641 80 96))) (mux (sgt v_9660 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9660 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9641 112 128))))))))));
      pure ()
    pat_end

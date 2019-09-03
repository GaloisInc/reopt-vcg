def packusdw1 : instruction :=
  definst "packusdw" $ do
    pattern fun (v_3093 : reg (bv 128)) (v_3094 : reg (bv 128)) => do
      v_5494 <- getRegister v_3093;
      v_5495 <- eval (extract v_5494 0 32);
      v_5501 <- eval (extract v_5494 32 64);
      v_5507 <- eval (extract v_5494 64 96);
      v_5513 <- eval (extract v_5494 96 128);
      v_5519 <- getRegister v_3094;
      v_5520 <- eval (extract v_5519 0 32);
      v_5526 <- eval (extract v_5519 32 64);
      v_5532 <- eval (extract v_5519 64 96);
      v_5538 <- eval (extract v_5519 96 128);
      setRegister (lhs.of_reg v_3094) (concat (mux (sgt v_5495 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5495 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5494 16 32))) (concat (mux (sgt v_5501 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5501 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5494 48 64))) (concat (mux (sgt v_5507 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5507 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5494 80 96))) (concat (mux (sgt v_5513 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5513 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5494 112 128))) (concat (mux (sgt v_5520 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5520 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5519 16 32))) (concat (mux (sgt v_5526 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5526 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5519 48 64))) (concat (mux (sgt v_5532 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5532 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5519 80 96))) (mux (sgt v_5538 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_5538 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_5519 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3088 : Mem) (v_3089 : reg (bv 128)) => do
      v_9596 <- evaluateAddress v_3088;
      v_9597 <- load v_9596 16;
      v_9598 <- eval (extract v_9597 0 32);
      v_9604 <- eval (extract v_9597 32 64);
      v_9610 <- eval (extract v_9597 64 96);
      v_9616 <- eval (extract v_9597 96 128);
      v_9622 <- getRegister v_3089;
      v_9623 <- eval (extract v_9622 0 32);
      v_9629 <- eval (extract v_9622 32 64);
      v_9635 <- eval (extract v_9622 64 96);
      v_9641 <- eval (extract v_9622 96 128);
      setRegister (lhs.of_reg v_3089) (concat (mux (sgt v_9598 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9598 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9597 16 32))) (concat (mux (sgt v_9604 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9604 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9597 48 64))) (concat (mux (sgt v_9610 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9610 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9597 80 96))) (concat (mux (sgt v_9616 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9616 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9597 112 128))) (concat (mux (sgt v_9623 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9623 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9622 16 32))) (concat (mux (sgt v_9629 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9629 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9622 48 64))) (concat (mux (sgt v_9635 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9635 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9622 80 96))) (mux (sgt v_9641 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_9641 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_9622 112 128))))))))));
      pure ()
    pat_end

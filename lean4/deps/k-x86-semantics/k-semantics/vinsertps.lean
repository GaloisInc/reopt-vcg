def vinsertps1 : instruction :=
  definst "vinsertps" $ do
    pattern fun (v_2542 : imm int) (v_2543 : reg (bv 128)) (v_2544 : reg (bv 128)) (v_2545 : reg (bv 128)) => do
      v_4280 <- eval (handleImmediateWithSignExtend v_2542 8 8);
      v_4282 <- eval (extract v_4280 2 4);
      v_4283 <- eval (eq v_4282 (expression.bv_nat 2 0));
      v_4284 <- getRegister v_2544;
      v_4285 <- eval (extract v_4284 0 32);
      v_4286 <- eval (eq v_4282 (expression.bv_nat 2 1));
      v_4287 <- eval (eq v_4282 (expression.bv_nat 2 2));
      v_4288 <- eval (extract v_4280 0 2);
      v_4290 <- getRegister v_2543;
      v_4299 <- eval (mux (eq v_4288 (expression.bv_nat 2 0)) (extract v_4290 96 128) (mux (eq v_4288 (expression.bv_nat 2 1)) (extract v_4290 64 96) (mux (eq v_4288 (expression.bv_nat 2 2)) (extract v_4290 32 64) (extract v_4290 0 32))));
      v_4305 <- eval (extract v_4284 32 64);
      v_4312 <- eval (extract v_4284 64 96);
      setRegister (lhs.of_reg v_2545) (concat (concat (concat (mux (isBitSet v_4280 4) (expression.bv_nat 32 0) (mux v_4283 v_4285 (mux v_4286 v_4285 (mux v_4287 v_4285 v_4299)))) (mux (isBitSet v_4280 5) (expression.bv_nat 32 0) (mux v_4283 v_4305 (mux v_4286 v_4305 (mux v_4287 v_4299 v_4305))))) (mux (isBitSet v_4280 6) (expression.bv_nat 32 0) (mux v_4283 v_4312 (mux v_4286 v_4299 v_4312)))) (mux (isBitSet v_4280 7) (expression.bv_nat 32 0) (mux v_4283 v_4299 (extract v_4284 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2536 : imm int) (v_2537 : Mem) (v_2538 : reg (bv 128)) (v_2539 : reg (bv 128)) => do
      v_9717 <- eval (handleImmediateWithSignExtend v_2536 8 8);
      v_9719 <- eval (extract v_9717 2 4);
      v_9720 <- eval (eq v_9719 (expression.bv_nat 2 0));
      v_9721 <- getRegister v_2538;
      v_9722 <- eval (extract v_9721 0 32);
      v_9723 <- eval (eq v_9719 (expression.bv_nat 2 1));
      v_9724 <- eval (eq v_9719 (expression.bv_nat 2 2));
      v_9725 <- evaluateAddress v_2537;
      v_9726 <- load v_9725 4;
      v_9732 <- eval (extract v_9721 32 64);
      v_9739 <- eval (extract v_9721 64 96);
      setRegister (lhs.of_reg v_2539) (concat (concat (concat (mux (isBitSet v_9717 4) (expression.bv_nat 32 0) (mux v_9720 v_9722 (mux v_9723 v_9722 (mux v_9724 v_9722 v_9726)))) (mux (isBitSet v_9717 5) (expression.bv_nat 32 0) (mux v_9720 v_9732 (mux v_9723 v_9732 (mux v_9724 v_9726 v_9732))))) (mux (isBitSet v_9717 6) (expression.bv_nat 32 0) (mux v_9720 v_9739 (mux v_9723 v_9726 v_9739)))) (mux (isBitSet v_9717 7) (expression.bv_nat 32 0) (mux v_9720 v_9726 (extract v_9721 96 128))));
      pure ()
    pat_end

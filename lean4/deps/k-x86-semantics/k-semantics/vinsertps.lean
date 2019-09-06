def vinsertps1 : instruction :=
  definst "vinsertps" $ do
    pattern fun (v_2567 : imm int) (v_2568 : reg (bv 128)) (v_2569 : reg (bv 128)) (v_2570 : reg (bv 128)) => do
      v_4307 <- eval (handleImmediateWithSignExtend v_2567 8 8);
      v_4309 <- eval (extract v_4307 2 4);
      v_4310 <- eval (eq v_4309 (expression.bv_nat 2 0));
      v_4311 <- getRegister v_2569;
      v_4312 <- eval (extract v_4311 0 32);
      v_4313 <- eval (eq v_4309 (expression.bv_nat 2 1));
      v_4314 <- eval (eq v_4309 (expression.bv_nat 2 2));
      v_4315 <- eval (extract v_4307 0 2);
      v_4317 <- getRegister v_2568;
      v_4326 <- eval (mux (eq v_4315 (expression.bv_nat 2 0)) (extract v_4317 96 128) (mux (eq v_4315 (expression.bv_nat 2 1)) (extract v_4317 64 96) (mux (eq v_4315 (expression.bv_nat 2 2)) (extract v_4317 32 64) (extract v_4317 0 32))));
      v_4332 <- eval (extract v_4311 32 64);
      v_4339 <- eval (extract v_4311 64 96);
      setRegister (lhs.of_reg v_2570) (concat (concat (concat (mux (isBitSet v_4307 4) (expression.bv_nat 32 0) (mux v_4310 v_4312 (mux v_4313 v_4312 (mux v_4314 v_4312 v_4326)))) (mux (isBitSet v_4307 5) (expression.bv_nat 32 0) (mux v_4310 v_4332 (mux v_4313 v_4332 (mux v_4314 v_4326 v_4332))))) (mux (isBitSet v_4307 6) (expression.bv_nat 32 0) (mux v_4310 v_4339 (mux v_4313 v_4326 v_4339)))) (mux (isBitSet v_4307 7) (expression.bv_nat 32 0) (mux v_4310 v_4326 (extract v_4311 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2561 : imm int) (v_2562 : Mem) (v_2563 : reg (bv 128)) (v_2564 : reg (bv 128)) => do
      v_9744 <- eval (handleImmediateWithSignExtend v_2561 8 8);
      v_9746 <- eval (extract v_9744 2 4);
      v_9747 <- eval (eq v_9746 (expression.bv_nat 2 0));
      v_9748 <- getRegister v_2563;
      v_9749 <- eval (extract v_9748 0 32);
      v_9750 <- eval (eq v_9746 (expression.bv_nat 2 1));
      v_9751 <- eval (eq v_9746 (expression.bv_nat 2 2));
      v_9752 <- evaluateAddress v_2562;
      v_9753 <- load v_9752 4;
      v_9759 <- eval (extract v_9748 32 64);
      v_9766 <- eval (extract v_9748 64 96);
      setRegister (lhs.of_reg v_2564) (concat (concat (concat (mux (isBitSet v_9744 4) (expression.bv_nat 32 0) (mux v_9747 v_9749 (mux v_9750 v_9749 (mux v_9751 v_9749 v_9753)))) (mux (isBitSet v_9744 5) (expression.bv_nat 32 0) (mux v_9747 v_9759 (mux v_9750 v_9759 (mux v_9751 v_9753 v_9759))))) (mux (isBitSet v_9744 6) (expression.bv_nat 32 0) (mux v_9747 v_9766 (mux v_9750 v_9753 v_9766)))) (mux (isBitSet v_9744 7) (expression.bv_nat 32 0) (mux v_9747 v_9753 (extract v_9748 96 128))));
      pure ()
    pat_end

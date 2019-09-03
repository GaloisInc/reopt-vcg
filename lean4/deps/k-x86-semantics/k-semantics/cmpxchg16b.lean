def cmpxchg16b1 : instruction :=
  definst "cmpxchg16b" $ do
    pattern fun (v_2432 : Mem) => do
      v_9376 <- evaluateAddress v_2432;
      v_9377 <- getRegister rdx;
      v_9378 <- getRegister rax;
      v_9379 <- eval (concat v_9377 v_9378);
      v_9380 <- load v_9376 16;
      v_9381 <- eval (eq v_9379 v_9380);
      v_9382 <- getRegister rcx;
      store v_9376 (mux v_9381 (concat v_9382 v_9376) v_9380) 16;
      setRegister rdx (mux v_9381 v_9377 (extract v_9380 0 64));
      setRegister rax (mux v_9381 v_9378 (extract v_9380 64 128));
      setRegister zf (mux (eq v_9380 v_9379) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

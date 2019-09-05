def cmpxchg16b1 : instruction :=
  definst "cmpxchg16b" $ do
    pattern fun (v_2496 : Mem) => do
      v_9016 <- evaluateAddress v_2496;
      v_9017 <- getRegister rdx;
      v_9018 <- getRegister rax;
      v_9019 <- eval (concat v_9017 v_9018);
      v_9020 <- load v_9016 16;
      v_9021 <- eval (eq v_9019 v_9020);
      v_9022 <- getRegister rcx;
      store v_9016 (mux v_9021 (concat v_9022 v_9016) v_9020) 16;
      setRegister rdx (mux v_9021 v_9017 (extract v_9020 0 64));
      setRegister rax (mux v_9021 v_9018 (extract v_9020 64 128));
      setRegister zf (eq v_9020 v_9019);
      pure ()
    pat_end

def cmpxchg16b1 : instruction :=
  definst "cmpxchg16b" $ do
    pattern fun (v_2523 : Mem) => do
      v_9026 <- evaluateAddress v_2523;
      v_9027 <- getRegister rdx;
      v_9028 <- getRegister rax;
      v_9029 <- eval (concat v_9027 v_9028);
      v_9030 <- load v_9026 16;
      v_9031 <- eval (eq v_9029 v_9030);
      v_9032 <- getRegister rcx;
      store v_9026 (mux v_9031 (concat v_9032 v_9026) v_9030) 16;
      setRegister rax (mux v_9031 v_9028 (extract v_9030 64 128));
      setRegister rdx (mux v_9031 v_9027 (extract v_9030 0 64));
      setRegister zf (eq v_9030 v_9029);
      pure ()
    pat_end

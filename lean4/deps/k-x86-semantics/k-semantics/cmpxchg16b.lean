def cmpxchg16b1 : instruction :=
  definst "cmpxchg16b" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- getRegister rdx;
      v_3 <- getRegister rax;
      v_4 <- eval (concat v_2 v_3);
      v_5 <- load v_1 16;
      v_6 <- eval (eq v_4 v_5);
      v_7 <- getRegister rcx;
      store v_1 (mux v_6 (concat v_7 v_1) v_5) 16;
      setRegister rax (mux v_6 v_3 (extract v_5 64 128));
      setRegister rdx (mux v_6 v_2 (extract v_5 0 64));
      setRegister zf (eq v_5 v_4);
      pure ()
    pat_end

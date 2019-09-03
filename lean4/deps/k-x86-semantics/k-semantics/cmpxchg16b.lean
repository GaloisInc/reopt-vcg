def cmpxchg16b1 : instruction :=
  definst "cmpxchg16b" $ do
    pattern fun (v_2443 : Mem) => do
      v_9966 <- evaluateAddress v_2443;
      v_9967 <- getRegister rdx;
      v_9968 <- getRegister rax;
      v_9969 <- eval (concat v_9967 v_9968);
      v_9970 <- load v_9966 16;
      v_9971 <- eval (eq v_9969 v_9970);
      v_9972 <- getRegister rcx;
      store v_9966 (mux v_9971 (concat v_9972 v_9966) v_9970) 16;
      setRegister rdx (mux v_9971 v_9967 (extract v_9970 0 64));
      setRegister rax (mux v_9971 v_9968 (extract v_9970 64 128));
      setRegister zf (mux (eq v_9970 v_9969) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

def cmpxchg8b : instruction :=
  definst "cmpxchg8b" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- getRegister rdx;
      (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      v_4 <- getRegister rax;
      (v_5 : expression (bv 32)) <- eval (extract v_4 32 64);
      v_6 <- load v_1 8;
      v_7 <- eval (eq (concat v_3 v_5) v_6);
      v_8 <- getRegister rcx;
      (v_9 : expression (bv 32)) <- eval (extract v_8 32 64);
      (v_10 : expression (bv 32)) <- eval (extract v_1 32 64);
      store v_1 (mux v_7 (concat v_9 v_10) v_6) 8;
      (v_12 : expression (bv 32)) <- eval (extract v_6 0 32);
      (v_13 : expression (bv 32)) <- eval (extract v_6 32 64);
      setRegister rax (mux v_7 v_4 (concat (expression.bv_nat 32 0) v_13));
      setRegister rdx (mux v_7 v_2 (concat (expression.bv_nat 32 0) v_12));
      setRegister zf v_7;
      pure ()
    pat_end

def cmpxchg8b1 : instruction :=
  definst "cmpxchg8b" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- getRegister rdx;
      v_3 <- getRegister rax;
      v_4 <- load v_1 8;
      v_5 <- eval (eq (concat (extract v_2 32 64) (extract v_3 32 64)) v_4);
      v_6 <- getRegister rcx;
      store v_1 (mux v_5 (concat (extract v_6 32 64) (extract v_1 32 64)) v_4) 8;
      setRegister rax (mux v_5 v_3 (concat (expression.bv_nat 32 0) (extract v_4 32 64)));
      setRegister rdx (mux v_5 v_2 (concat (expression.bv_nat 32 0) (extract v_4 0 32)));
      setRegister zf v_5;
      pure ()
    pat_end

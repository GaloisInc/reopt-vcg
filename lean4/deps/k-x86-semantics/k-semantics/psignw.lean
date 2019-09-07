def psignw1 : instruction :=
  definst "psignw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (extract v_3 0 16);
      v_5 <- getRegister xmm_1;
      v_6 <- eval (extract v_5 0 16);
      v_7 <- eval (extract v_3 16 32);
      v_8 <- eval (extract v_5 16 32);
      v_9 <- eval (extract v_3 32 48);
      v_10 <- eval (extract v_5 32 48);
      v_11 <- eval (extract v_3 48 64);
      v_12 <- eval (extract v_5 48 64);
      v_13 <- eval (extract v_3 64 80);
      v_14 <- eval (extract v_5 64 80);
      v_15 <- eval (extract v_3 80 96);
      v_16 <- eval (extract v_5 80 96);
      v_17 <- eval (extract v_3 96 112);
      v_18 <- eval (extract v_5 96 112);
      v_19 <- eval (extract v_3 112 128);
      v_20 <- eval (extract v_5 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 16 0)) v_6 (mux (eq v_4 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_7 (expression.bv_nat 16 0)) v_8 (mux (eq v_7 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_9 (expression.bv_nat 16 0)) v_10 (mux (eq v_9 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_11 (expression.bv_nat 16 0)) v_12 (mux (eq v_11 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_12 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_13 (expression.bv_nat 16 0)) v_14 (mux (eq v_13 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_14 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_15 (expression.bv_nat 16 0)) v_16 (mux (eq v_15 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_16 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_17 (expression.bv_nat 16 0)) v_18 (mux (eq v_17 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_18 (expression.bv_nat 16 65535))))) (mux (sgt v_19 (expression.bv_nat 16 0)) v_20 (mux (eq v_19 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_20 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- eval (extract v_2 0 16);
      v_4 <- getRegister xmm_1;
      v_5 <- eval (extract v_4 0 16);
      v_6 <- eval (extract v_2 16 32);
      v_7 <- eval (extract v_4 16 32);
      v_8 <- eval (extract v_2 32 48);
      v_9 <- eval (extract v_4 32 48);
      v_10 <- eval (extract v_2 48 64);
      v_11 <- eval (extract v_4 48 64);
      v_12 <- eval (extract v_2 64 80);
      v_13 <- eval (extract v_4 64 80);
      v_14 <- eval (extract v_2 80 96);
      v_15 <- eval (extract v_4 80 96);
      v_16 <- eval (extract v_2 96 112);
      v_17 <- eval (extract v_4 96 112);
      v_18 <- eval (extract v_2 112 128);
      v_19 <- eval (extract v_4 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_3 (expression.bv_nat 16 0)) v_5 (mux (eq v_3 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_6 (expression.bv_nat 16 0)) v_7 (mux (eq v_6 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_8 (expression.bv_nat 16 0)) v_9 (mux (eq v_8 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_10 (expression.bv_nat 16 0)) v_11 (mux (eq v_10 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_11 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_12 (expression.bv_nat 16 0)) v_13 (mux (eq v_12 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_13 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_14 (expression.bv_nat 16 0)) v_15 (mux (eq v_14 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_15 (expression.bv_nat 16 65535))))) (concat (mux (sgt v_16 (expression.bv_nat 16 0)) v_17 (mux (eq v_16 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_17 (expression.bv_nat 16 65535))))) (mux (sgt v_18 (expression.bv_nat 16 0)) v_19 (mux (eq v_18 (expression.bv_nat 16 0)) (expression.bv_nat 16 0) (add (expression.bv_nat 16 1) (bv_xor v_19 (expression.bv_nat 16 65535))))))))))));
      pure ()
    pat_end

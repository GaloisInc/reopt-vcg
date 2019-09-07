def psubusw1 : instruction :=
  definst "psubusw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 0 16)) (concat (expression.bv_nat 2 0) (extract v_4 0 16)));
      v_6 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 16 32)) (concat (expression.bv_nat 2 0) (extract v_4 16 32)));
      v_7 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 32 48)) (concat (expression.bv_nat 2 0) (extract v_4 32 48)));
      v_8 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 48 64)) (concat (expression.bv_nat 2 0) (extract v_4 48 64)));
      v_9 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 64 80)) (concat (expression.bv_nat 2 0) (extract v_4 64 80)));
      v_10 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 80 96)) (concat (expression.bv_nat 2 0) (extract v_4 80 96)));
      v_11 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 96 112)) (concat (expression.bv_nat 2 0) (extract v_4 96 112)));
      v_12 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 112 128)) (concat (expression.bv_nat 2 0) (extract v_4 112 128)));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_5 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5 2 18))) (concat (mux (sgt v_6 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_6 2 18))) (concat (mux (sgt v_7 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_7 2 18))) (concat (mux (sgt v_8 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8 2 18))) (concat (mux (sgt v_9 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_9 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_9 2 18))) (concat (mux (sgt v_10 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_10 2 18))) (concat (mux (sgt v_11 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11 2 18))) (mux (sgt v_12 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_12 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_12 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      v_4 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 0 16)) (concat (expression.bv_nat 2 0) (extract v_3 0 16)));
      v_5 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 16 32)) (concat (expression.bv_nat 2 0) (extract v_3 16 32)));
      v_6 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 32 48)) (concat (expression.bv_nat 2 0) (extract v_3 32 48)));
      v_7 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 48 64)) (concat (expression.bv_nat 2 0) (extract v_3 48 64)));
      v_8 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 64 80)) (concat (expression.bv_nat 2 0) (extract v_3 64 80)));
      v_9 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 80 96)) (concat (expression.bv_nat 2 0) (extract v_3 80 96)));
      v_10 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 96 112)) (concat (expression.bv_nat 2 0) (extract v_3 96 112)));
      v_11 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_2 112 128)) (concat (expression.bv_nat 2 0) (extract v_3 112 128)));
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_4 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_4 2 18))) (concat (mux (sgt v_5 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_5 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_5 2 18))) (concat (mux (sgt v_6 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_6 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_6 2 18))) (concat (mux (sgt v_7 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_7 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_7 2 18))) (concat (mux (sgt v_8 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8 2 18))) (concat (mux (sgt v_9 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_9 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_9 2 18))) (concat (mux (sgt v_10 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_10 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_10 2 18))) (mux (sgt v_11 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_11 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_11 2 18))))))))));
      pure ()
    pat_end

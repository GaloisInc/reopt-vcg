def packuswb1 : instruction :=
  definst "packuswb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (extract v_3 0 16);
      v_5 <- eval (extract v_3 16 32);
      v_6 <- eval (extract v_3 32 48);
      v_7 <- eval (extract v_3 48 64);
      v_8 <- eval (extract v_3 64 80);
      v_9 <- eval (extract v_3 80 96);
      v_10 <- eval (extract v_3 96 112);
      v_11 <- eval (extract v_3 112 128);
      v_12 <- getRegister xmm_1;
      v_13 <- eval (extract v_12 0 16);
      v_14 <- eval (extract v_12 16 32);
      v_15 <- eval (extract v_12 32 48);
      v_16 <- eval (extract v_12 48 64);
      v_17 <- eval (extract v_12 64 80);
      v_18 <- eval (extract v_12 80 96);
      v_19 <- eval (extract v_12 96 112);
      v_20 <- eval (extract v_12 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_4 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_4 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_3 8 16))) (concat (mux (sgt v_5 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_3 24 32))) (concat (mux (sgt v_6 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_6 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_3 40 48))) (concat (mux (sgt v_7 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_7 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_3 56 64))) (concat (mux (sgt v_8 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_8 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_3 72 80))) (concat (mux (sgt v_9 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_3 88 96))) (concat (mux (sgt v_10 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_10 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_3 104 112))) (concat (mux (sgt v_11 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_11 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_3 120 128))) (concat (mux (sgt v_13 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_13 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_12 8 16))) (concat (mux (sgt v_14 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_14 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_12 24 32))) (concat (mux (sgt v_15 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_15 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_12 40 48))) (concat (mux (sgt v_16 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_16 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_12 56 64))) (concat (mux (sgt v_17 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_17 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_12 72 80))) (concat (mux (sgt v_18 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_18 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_12 88 96))) (concat (mux (sgt v_19 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_19 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_12 104 112))) (mux (sgt v_20 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_20 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_12 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- eval (extract v_2 0 16);
      v_4 <- eval (extract v_2 16 32);
      v_5 <- eval (extract v_2 32 48);
      v_6 <- eval (extract v_2 48 64);
      v_7 <- eval (extract v_2 64 80);
      v_8 <- eval (extract v_2 80 96);
      v_9 <- eval (extract v_2 96 112);
      v_10 <- eval (extract v_2 112 128);
      v_11 <- getRegister xmm_1;
      v_12 <- eval (extract v_11 0 16);
      v_13 <- eval (extract v_11 16 32);
      v_14 <- eval (extract v_11 32 48);
      v_15 <- eval (extract v_11 48 64);
      v_16 <- eval (extract v_11 64 80);
      v_17 <- eval (extract v_11 80 96);
      v_18 <- eval (extract v_11 96 112);
      v_19 <- eval (extract v_11 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (sgt v_3 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_3 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_2 8 16))) (concat (mux (sgt v_4 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_4 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_2 24 32))) (concat (mux (sgt v_5 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_2 40 48))) (concat (mux (sgt v_6 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_6 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_2 56 64))) (concat (mux (sgt v_7 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_7 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_2 72 80))) (concat (mux (sgt v_8 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_8 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_2 88 96))) (concat (mux (sgt v_9 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_2 104 112))) (concat (mux (sgt v_10 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_10 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_2 120 128))) (concat (mux (sgt v_12 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_12 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_11 8 16))) (concat (mux (sgt v_13 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_13 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_11 24 32))) (concat (mux (sgt v_14 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_14 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_11 40 48))) (concat (mux (sgt v_15 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_15 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_11 56 64))) (concat (mux (sgt v_16 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_16 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_11 72 80))) (concat (mux (sgt v_17 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_17 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_11 88 96))) (concat (mux (sgt v_18 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_18 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_11 104 112))) (mux (sgt v_19 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_19 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_11 120 128))))))))))))))))));
      pure ()
    pat_end

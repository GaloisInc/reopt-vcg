def pabsb1 : instruction :=
  definst "pabsb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (extract v_3 0 8);
      v_5 <- eval (extract v_3 8 16);
      v_6 <- eval (extract v_3 16 24);
      v_7 <- eval (extract v_3 24 32);
      v_8 <- eval (extract v_3 32 40);
      v_9 <- eval (extract v_3 40 48);
      v_10 <- eval (extract v_3 48 56);
      v_11 <- eval (extract v_3 56 64);
      v_12 <- eval (extract v_3 64 72);
      v_13 <- eval (extract v_3 72 80);
      v_14 <- eval (extract v_3 80 88);
      v_15 <- eval (extract v_3 88 96);
      v_16 <- eval (extract v_3 96 104);
      v_17 <- eval (extract v_3 104 112);
      v_18 <- eval (extract v_3 112 120);
      v_19 <- eval (extract v_3 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ugt v_4 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_4 (expression.bv_nat 8 255))) v_4) (concat (mux (ugt v_5 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5 (expression.bv_nat 8 255))) v_5) (concat (mux (ugt v_6 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_6 (expression.bv_nat 8 255))) v_6) (concat (mux (ugt v_7 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_7 (expression.bv_nat 8 255))) v_7) (concat (mux (ugt v_8 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_8 (expression.bv_nat 8 255))) v_8) (concat (mux (ugt v_9 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9 (expression.bv_nat 8 255))) v_9) (concat (mux (ugt v_10 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_10 (expression.bv_nat 8 255))) v_10) (concat (mux (ugt v_11 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_11 (expression.bv_nat 8 255))) v_11) (concat (mux (ugt v_12 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_12 (expression.bv_nat 8 255))) v_12) (concat (mux (ugt v_13 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_13 (expression.bv_nat 8 255))) v_13) (concat (mux (ugt v_14 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_14 (expression.bv_nat 8 255))) v_14) (concat (mux (ugt v_15 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_15 (expression.bv_nat 8 255))) v_15) (concat (mux (ugt v_16 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_16 (expression.bv_nat 8 255))) v_16) (concat (mux (ugt v_17 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_17 (expression.bv_nat 8 255))) v_17) (concat (mux (ugt v_18 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_18 (expression.bv_nat 8 255))) v_18) (mux (ugt v_19 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_19 (expression.bv_nat 8 255))) v_19))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- eval (extract v_2 0 8);
      v_4 <- eval (extract v_2 8 16);
      v_5 <- eval (extract v_2 16 24);
      v_6 <- eval (extract v_2 24 32);
      v_7 <- eval (extract v_2 32 40);
      v_8 <- eval (extract v_2 40 48);
      v_9 <- eval (extract v_2 48 56);
      v_10 <- eval (extract v_2 56 64);
      v_11 <- eval (extract v_2 64 72);
      v_12 <- eval (extract v_2 72 80);
      v_13 <- eval (extract v_2 80 88);
      v_14 <- eval (extract v_2 88 96);
      v_15 <- eval (extract v_2 96 104);
      v_16 <- eval (extract v_2 104 112);
      v_17 <- eval (extract v_2 112 120);
      v_18 <- eval (extract v_2 120 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ugt v_3 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_3 (expression.bv_nat 8 255))) v_3) (concat (mux (ugt v_4 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_4 (expression.bv_nat 8 255))) v_4) (concat (mux (ugt v_5 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_5 (expression.bv_nat 8 255))) v_5) (concat (mux (ugt v_6 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_6 (expression.bv_nat 8 255))) v_6) (concat (mux (ugt v_7 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_7 (expression.bv_nat 8 255))) v_7) (concat (mux (ugt v_8 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_8 (expression.bv_nat 8 255))) v_8) (concat (mux (ugt v_9 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_9 (expression.bv_nat 8 255))) v_9) (concat (mux (ugt v_10 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_10 (expression.bv_nat 8 255))) v_10) (concat (mux (ugt v_11 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_11 (expression.bv_nat 8 255))) v_11) (concat (mux (ugt v_12 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_12 (expression.bv_nat 8 255))) v_12) (concat (mux (ugt v_13 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_13 (expression.bv_nat 8 255))) v_13) (concat (mux (ugt v_14 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_14 (expression.bv_nat 8 255))) v_14) (concat (mux (ugt v_15 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_15 (expression.bv_nat 8 255))) v_15) (concat (mux (ugt v_16 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_16 (expression.bv_nat 8 255))) v_16) (concat (mux (ugt v_17 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_17 (expression.bv_nat 8 255))) v_17) (mux (ugt v_18 (expression.bv_nat 8 127)) (add (expression.bv_nat 8 1) (bv_xor v_18 (expression.bv_nat 8 255))) v_18))))))))))))))));
      pure ()
    pat_end

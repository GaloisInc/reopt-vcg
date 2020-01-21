def vpabsw : instruction :=
  definst "vpabsw" $ do
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
      setRegister (lhs.of_reg xmm_1) (concat (mux (ugt v_4 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_4 (expression.bv_nat 16 65535))) v_4) (concat (mux (ugt v_5 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))) v_5) (concat (mux (ugt v_6 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))) v_6) (concat (mux (ugt v_7 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))) v_7) (concat (mux (ugt v_8 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))) v_8) (concat (mux (ugt v_9 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))) v_9) (concat (mux (ugt v_10 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))) v_10) (mux (ugt v_11 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11 (expression.bv_nat 16 65535))) v_11))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      v_4 <- eval (extract v_3 0 16);
      v_5 <- eval (extract v_3 16 32);
      v_6 <- eval (extract v_3 32 48);
      v_7 <- eval (extract v_3 48 64);
      v_8 <- eval (extract v_3 64 80);
      v_9 <- eval (extract v_3 80 96);
      v_10 <- eval (extract v_3 96 112);
      v_11 <- eval (extract v_3 112 128);
      v_12 <- eval (extract v_3 128 144);
      v_13 <- eval (extract v_3 144 160);
      v_14 <- eval (extract v_3 160 176);
      v_15 <- eval (extract v_3 176 192);
      v_16 <- eval (extract v_3 192 208);
      v_17 <- eval (extract v_3 208 224);
      v_18 <- eval (extract v_3 224 240);
      v_19 <- eval (extract v_3 240 256);
      setRegister (lhs.of_reg ymm_1) (concat (mux (ugt v_4 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_4 (expression.bv_nat 16 65535))) v_4) (concat (mux (ugt v_5 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))) v_5) (concat (mux (ugt v_6 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))) v_6) (concat (mux (ugt v_7 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))) v_7) (concat (mux (ugt v_8 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))) v_8) (concat (mux (ugt v_9 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))) v_9) (concat (mux (ugt v_10 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))) v_10) (concat (mux (ugt v_11 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11 (expression.bv_nat 16 65535))) v_11) (concat (mux (ugt v_12 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12 (expression.bv_nat 16 65535))) v_12) (concat (mux (ugt v_13 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_13 (expression.bv_nat 16 65535))) v_13) (concat (mux (ugt v_14 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_14 (expression.bv_nat 16 65535))) v_14) (concat (mux (ugt v_15 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_15 (expression.bv_nat 16 65535))) v_15) (concat (mux (ugt v_16 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_16 (expression.bv_nat 16 65535))) v_16) (concat (mux (ugt v_17 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_17 (expression.bv_nat 16 65535))) v_17) (concat (mux (ugt v_18 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_18 (expression.bv_nat 16 65535))) v_18) (mux (ugt v_19 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_19 (expression.bv_nat 16 65535))) v_19))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      v_3 <- eval (extract v_2 0 16);
      v_4 <- eval (extract v_2 16 32);
      v_5 <- eval (extract v_2 32 48);
      v_6 <- eval (extract v_2 48 64);
      v_7 <- eval (extract v_2 64 80);
      v_8 <- eval (extract v_2 80 96);
      v_9 <- eval (extract v_2 96 112);
      v_10 <- eval (extract v_2 112 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (ugt v_3 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_3 (expression.bv_nat 16 65535))) v_3) (concat (mux (ugt v_4 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_4 (expression.bv_nat 16 65535))) v_4) (concat (mux (ugt v_5 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))) v_5) (concat (mux (ugt v_6 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))) v_6) (concat (mux (ugt v_7 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))) v_7) (concat (mux (ugt v_8 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))) v_8) (concat (mux (ugt v_9 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))) v_9) (mux (ugt v_10 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))) v_10))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      v_3 <- eval (extract v_2 0 16);
      v_4 <- eval (extract v_2 16 32);
      v_5 <- eval (extract v_2 32 48);
      v_6 <- eval (extract v_2 48 64);
      v_7 <- eval (extract v_2 64 80);
      v_8 <- eval (extract v_2 80 96);
      v_9 <- eval (extract v_2 96 112);
      v_10 <- eval (extract v_2 112 128);
      v_11 <- eval (extract v_2 128 144);
      v_12 <- eval (extract v_2 144 160);
      v_13 <- eval (extract v_2 160 176);
      v_14 <- eval (extract v_2 176 192);
      v_15 <- eval (extract v_2 192 208);
      v_16 <- eval (extract v_2 208 224);
      v_17 <- eval (extract v_2 224 240);
      v_18 <- eval (extract v_2 240 256);
      setRegister (lhs.of_reg ymm_1) (concat (mux (ugt v_3 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_3 (expression.bv_nat 16 65535))) v_3) (concat (mux (ugt v_4 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_4 (expression.bv_nat 16 65535))) v_4) (concat (mux (ugt v_5 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_5 (expression.bv_nat 16 65535))) v_5) (concat (mux (ugt v_6 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_6 (expression.bv_nat 16 65535))) v_6) (concat (mux (ugt v_7 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_7 (expression.bv_nat 16 65535))) v_7) (concat (mux (ugt v_8 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_8 (expression.bv_nat 16 65535))) v_8) (concat (mux (ugt v_9 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_9 (expression.bv_nat 16 65535))) v_9) (concat (mux (ugt v_10 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_10 (expression.bv_nat 16 65535))) v_10) (concat (mux (ugt v_11 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_11 (expression.bv_nat 16 65535))) v_11) (concat (mux (ugt v_12 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_12 (expression.bv_nat 16 65535))) v_12) (concat (mux (ugt v_13 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_13 (expression.bv_nat 16 65535))) v_13) (concat (mux (ugt v_14 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_14 (expression.bv_nat 16 65535))) v_14) (concat (mux (ugt v_15 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_15 (expression.bv_nat 16 65535))) v_15) (concat (mux (ugt v_16 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_16 (expression.bv_nat 16 65535))) v_16) (concat (mux (ugt v_17 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_17 (expression.bv_nat 16 65535))) v_17) (mux (ugt v_18 (expression.bv_nat 16 32767)) (add (expression.bv_nat 16 1) (bv_xor v_18 (expression.bv_nat 16 65535))) v_18))))))))))))))));
      pure ()
    pat_end

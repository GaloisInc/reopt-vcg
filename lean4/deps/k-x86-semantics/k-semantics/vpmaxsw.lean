def vpmaxsw : instruction :=
  definst "vpmaxsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_6 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_6 48 64);
      (v_14 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_6 64 80);
      (v_16 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_17 : expression (bv 16)) <- eval (extract v_6 80 96);
      (v_18 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_6 96 112);
      (v_20 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_21 : expression (bv 16)) <- eval (extract v_6 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_4 v_7) v_4 v_7) (concat (mux (sgt v_8 v_9) v_8 v_9) (concat (mux (sgt v_10 v_11) v_10 v_11) (concat (mux (sgt v_12 v_13) v_12 v_13) (concat (mux (sgt v_14 v_15) v_14 v_15) (concat (mux (sgt v_16 v_17) v_16 v_17) (concat (mux (sgt v_18 v_19) v_18 v_19) (mux (sgt v_20 v_21) v_20 v_21))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      (v_8 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_6 16 32);
      (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_6 32 48);
      (v_12 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_6 48 64);
      (v_14 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_6 64 80);
      (v_16 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_17 : expression (bv 16)) <- eval (extract v_6 80 96);
      (v_18 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_6 96 112);
      (v_20 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_21 : expression (bv 16)) <- eval (extract v_6 112 128);
      (v_22 : expression (bv 16)) <- eval (extract v_3 128 144);
      (v_23 : expression (bv 16)) <- eval (extract v_6 128 144);
      (v_24 : expression (bv 16)) <- eval (extract v_3 144 160);
      (v_25 : expression (bv 16)) <- eval (extract v_6 144 160);
      (v_26 : expression (bv 16)) <- eval (extract v_3 160 176);
      (v_27 : expression (bv 16)) <- eval (extract v_6 160 176);
      (v_28 : expression (bv 16)) <- eval (extract v_3 176 192);
      (v_29 : expression (bv 16)) <- eval (extract v_6 176 192);
      (v_30 : expression (bv 16)) <- eval (extract v_3 192 208);
      (v_31 : expression (bv 16)) <- eval (extract v_6 192 208);
      (v_32 : expression (bv 16)) <- eval (extract v_3 208 224);
      (v_33 : expression (bv 16)) <- eval (extract v_6 208 224);
      (v_34 : expression (bv 16)) <- eval (extract v_3 224 240);
      (v_35 : expression (bv 16)) <- eval (extract v_6 224 240);
      (v_36 : expression (bv 16)) <- eval (extract v_3 240 256);
      (v_37 : expression (bv 16)) <- eval (extract v_6 240 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_4 v_7) v_4 v_7) (concat (mux (sgt v_8 v_9) v_8 v_9) (concat (mux (sgt v_10 v_11) v_10 v_11) (concat (mux (sgt v_12 v_13) v_12 v_13) (concat (mux (sgt v_14 v_15) v_14 v_15) (concat (mux (sgt v_16 v_17) v_16 v_17) (concat (mux (sgt v_18 v_19) v_18 v_19) (concat (mux (sgt v_20 v_21) v_20 v_21) (concat (mux (sgt v_22 v_23) v_22 v_23) (concat (mux (sgt v_24 v_25) v_24 v_25) (concat (mux (sgt v_26 v_27) v_26 v_27) (concat (mux (sgt v_28 v_29) v_28 v_29) (concat (mux (sgt v_30 v_31) v_30 v_31) (concat (mux (sgt v_32 v_33) v_32 v_33) (concat (mux (sgt v_34 v_35) v_34 v_35) (mux (sgt v_36 v_37) v_36 v_37))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_10 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_14 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_16 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_17 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_18 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_20 : expression (bv 16)) <- eval (extract v_5 112 128);
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_4 v_6) v_4 v_6) (concat (mux (sgt v_7 v_8) v_7 v_8) (concat (mux (sgt v_9 v_10) v_9 v_10) (concat (mux (sgt v_11 v_12) v_11 v_12) (concat (mux (sgt v_13 v_14) v_13 v_14) (concat (mux (sgt v_15 v_16) v_15 v_16) (concat (mux (sgt v_17 v_18) v_17 v_18) (mux (sgt v_19 v_20) v_19 v_20))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      (v_8 : expression (bv 16)) <- eval (extract v_5 16 32);
      (v_9 : expression (bv 16)) <- eval (extract v_3 32 48);
      (v_10 : expression (bv 16)) <- eval (extract v_5 32 48);
      (v_11 : expression (bv 16)) <- eval (extract v_3 48 64);
      (v_12 : expression (bv 16)) <- eval (extract v_5 48 64);
      (v_13 : expression (bv 16)) <- eval (extract v_3 64 80);
      (v_14 : expression (bv 16)) <- eval (extract v_5 64 80);
      (v_15 : expression (bv 16)) <- eval (extract v_3 80 96);
      (v_16 : expression (bv 16)) <- eval (extract v_5 80 96);
      (v_17 : expression (bv 16)) <- eval (extract v_3 96 112);
      (v_18 : expression (bv 16)) <- eval (extract v_5 96 112);
      (v_19 : expression (bv 16)) <- eval (extract v_3 112 128);
      (v_20 : expression (bv 16)) <- eval (extract v_5 112 128);
      (v_21 : expression (bv 16)) <- eval (extract v_3 128 144);
      (v_22 : expression (bv 16)) <- eval (extract v_5 128 144);
      (v_23 : expression (bv 16)) <- eval (extract v_3 144 160);
      (v_24 : expression (bv 16)) <- eval (extract v_5 144 160);
      (v_25 : expression (bv 16)) <- eval (extract v_3 160 176);
      (v_26 : expression (bv 16)) <- eval (extract v_5 160 176);
      (v_27 : expression (bv 16)) <- eval (extract v_3 176 192);
      (v_28 : expression (bv 16)) <- eval (extract v_5 176 192);
      (v_29 : expression (bv 16)) <- eval (extract v_3 192 208);
      (v_30 : expression (bv 16)) <- eval (extract v_5 192 208);
      (v_31 : expression (bv 16)) <- eval (extract v_3 208 224);
      (v_32 : expression (bv 16)) <- eval (extract v_5 208 224);
      (v_33 : expression (bv 16)) <- eval (extract v_3 224 240);
      (v_34 : expression (bv 16)) <- eval (extract v_5 224 240);
      (v_35 : expression (bv 16)) <- eval (extract v_3 240 256);
      (v_36 : expression (bv 16)) <- eval (extract v_5 240 256);
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_4 v_6) v_4 v_6) (concat (mux (sgt v_7 v_8) v_7 v_8) (concat (mux (sgt v_9 v_10) v_9 v_10) (concat (mux (sgt v_11 v_12) v_11 v_12) (concat (mux (sgt v_13 v_14) v_13 v_14) (concat (mux (sgt v_15 v_16) v_15 v_16) (concat (mux (sgt v_17 v_18) v_17 v_18) (concat (mux (sgt v_19 v_20) v_19 v_20) (concat (mux (sgt v_21 v_22) v_21 v_22) (concat (mux (sgt v_23 v_24) v_23 v_24) (concat (mux (sgt v_25 v_26) v_25 v_26) (concat (mux (sgt v_27 v_28) v_27 v_28) (concat (mux (sgt v_29 v_30) v_29 v_30) (concat (mux (sgt v_31 v_32) v_31 v_32) (concat (mux (sgt v_33 v_34) v_33 v_34) (mux (sgt v_35 v_36) v_35 v_36))))))))))))))));
      pure ()
    pat_end

def pshufb1 : instruction :=
  definst "pshufb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (extract v_3 4 8);
      v_5 <- getRegister xmm_1;
      v_6 <- eval (extract v_5 0 8);
      v_7 <- eval (extract v_5 8 16);
      v_8 <- eval (extract v_5 16 24);
      v_9 <- eval (extract v_5 24 32);
      v_10 <- eval (extract v_5 32 40);
      v_11 <- eval (extract v_5 40 48);
      v_12 <- eval (extract v_5 48 56);
      v_13 <- eval (extract v_5 56 64);
      v_14 <- eval (extract v_5 64 72);
      v_15 <- eval (extract v_5 72 80);
      v_16 <- eval (extract v_5 80 88);
      v_17 <- eval (extract v_5 88 96);
      v_18 <- eval (extract v_5 96 104);
      v_19 <- eval (extract v_5 104 112);
      v_20 <- eval (extract v_5 112 120);
      v_21 <- eval (extract v_5 120 128);
      v_22 <- eval (extract v_3 12 16);
      v_23 <- eval (extract v_3 20 24);
      v_24 <- eval (extract v_3 28 32);
      v_25 <- eval (extract v_3 36 40);
      v_26 <- eval (extract v_3 44 48);
      v_27 <- eval (extract v_3 52 56);
      v_28 <- eval (extract v_3 60 64);
      v_29 <- eval (extract v_3 68 72);
      v_30 <- eval (extract v_3 76 80);
      v_31 <- eval (extract v_3 84 88);
      v_32 <- eval (extract v_3 92 96);
      v_33 <- eval (extract v_3 100 104);
      v_34 <- eval (extract v_3 108 112);
      v_35 <- eval (extract v_3 116 120);
      v_36 <- eval (extract v_3 124 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (isBitSet v_3 0) (expression.bv_nat 8 0) (mux (eq v_4 (expression.bv_nat 4 15)) v_6 (mux (eq v_4 (expression.bv_nat 4 14)) v_7 (mux (eq v_4 (expression.bv_nat 4 13)) v_8 (mux (eq v_4 (expression.bv_nat 4 12)) v_9 (mux (eq v_4 (expression.bv_nat 4 11)) v_10 (mux (eq v_4 (expression.bv_nat 4 10)) v_11 (mux (eq v_4 (expression.bv_nat 4 9)) v_12 (mux (eq v_4 (expression.bv_nat 4 8)) v_13 (mux (eq v_4 (expression.bv_nat 4 7)) v_14 (mux (eq v_4 (expression.bv_nat 4 6)) v_15 (mux (eq v_4 (expression.bv_nat 4 5)) v_16 (mux (eq v_4 (expression.bv_nat 4 4)) v_17 (mux (eq v_4 (expression.bv_nat 4 3)) v_18 (mux (eq v_4 (expression.bv_nat 4 2)) v_19 (mux (eq v_4 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 8) (expression.bv_nat 8 0) (mux (eq v_22 (expression.bv_nat 4 15)) v_6 (mux (eq v_22 (expression.bv_nat 4 14)) v_7 (mux (eq v_22 (expression.bv_nat 4 13)) v_8 (mux (eq v_22 (expression.bv_nat 4 12)) v_9 (mux (eq v_22 (expression.bv_nat 4 11)) v_10 (mux (eq v_22 (expression.bv_nat 4 10)) v_11 (mux (eq v_22 (expression.bv_nat 4 9)) v_12 (mux (eq v_22 (expression.bv_nat 4 8)) v_13 (mux (eq v_22 (expression.bv_nat 4 7)) v_14 (mux (eq v_22 (expression.bv_nat 4 6)) v_15 (mux (eq v_22 (expression.bv_nat 4 5)) v_16 (mux (eq v_22 (expression.bv_nat 4 4)) v_17 (mux (eq v_22 (expression.bv_nat 4 3)) v_18 (mux (eq v_22 (expression.bv_nat 4 2)) v_19 (mux (eq v_22 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 16) (expression.bv_nat 8 0) (mux (eq v_23 (expression.bv_nat 4 15)) v_6 (mux (eq v_23 (expression.bv_nat 4 14)) v_7 (mux (eq v_23 (expression.bv_nat 4 13)) v_8 (mux (eq v_23 (expression.bv_nat 4 12)) v_9 (mux (eq v_23 (expression.bv_nat 4 11)) v_10 (mux (eq v_23 (expression.bv_nat 4 10)) v_11 (mux (eq v_23 (expression.bv_nat 4 9)) v_12 (mux (eq v_23 (expression.bv_nat 4 8)) v_13 (mux (eq v_23 (expression.bv_nat 4 7)) v_14 (mux (eq v_23 (expression.bv_nat 4 6)) v_15 (mux (eq v_23 (expression.bv_nat 4 5)) v_16 (mux (eq v_23 (expression.bv_nat 4 4)) v_17 (mux (eq v_23 (expression.bv_nat 4 3)) v_18 (mux (eq v_23 (expression.bv_nat 4 2)) v_19 (mux (eq v_23 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 24) (expression.bv_nat 8 0) (mux (eq v_24 (expression.bv_nat 4 15)) v_6 (mux (eq v_24 (expression.bv_nat 4 14)) v_7 (mux (eq v_24 (expression.bv_nat 4 13)) v_8 (mux (eq v_24 (expression.bv_nat 4 12)) v_9 (mux (eq v_24 (expression.bv_nat 4 11)) v_10 (mux (eq v_24 (expression.bv_nat 4 10)) v_11 (mux (eq v_24 (expression.bv_nat 4 9)) v_12 (mux (eq v_24 (expression.bv_nat 4 8)) v_13 (mux (eq v_24 (expression.bv_nat 4 7)) v_14 (mux (eq v_24 (expression.bv_nat 4 6)) v_15 (mux (eq v_24 (expression.bv_nat 4 5)) v_16 (mux (eq v_24 (expression.bv_nat 4 4)) v_17 (mux (eq v_24 (expression.bv_nat 4 3)) v_18 (mux (eq v_24 (expression.bv_nat 4 2)) v_19 (mux (eq v_24 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 32) (expression.bv_nat 8 0) (mux (eq v_25 (expression.bv_nat 4 15)) v_6 (mux (eq v_25 (expression.bv_nat 4 14)) v_7 (mux (eq v_25 (expression.bv_nat 4 13)) v_8 (mux (eq v_25 (expression.bv_nat 4 12)) v_9 (mux (eq v_25 (expression.bv_nat 4 11)) v_10 (mux (eq v_25 (expression.bv_nat 4 10)) v_11 (mux (eq v_25 (expression.bv_nat 4 9)) v_12 (mux (eq v_25 (expression.bv_nat 4 8)) v_13 (mux (eq v_25 (expression.bv_nat 4 7)) v_14 (mux (eq v_25 (expression.bv_nat 4 6)) v_15 (mux (eq v_25 (expression.bv_nat 4 5)) v_16 (mux (eq v_25 (expression.bv_nat 4 4)) v_17 (mux (eq v_25 (expression.bv_nat 4 3)) v_18 (mux (eq v_25 (expression.bv_nat 4 2)) v_19 (mux (eq v_25 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 40) (expression.bv_nat 8 0) (mux (eq v_26 (expression.bv_nat 4 15)) v_6 (mux (eq v_26 (expression.bv_nat 4 14)) v_7 (mux (eq v_26 (expression.bv_nat 4 13)) v_8 (mux (eq v_26 (expression.bv_nat 4 12)) v_9 (mux (eq v_26 (expression.bv_nat 4 11)) v_10 (mux (eq v_26 (expression.bv_nat 4 10)) v_11 (mux (eq v_26 (expression.bv_nat 4 9)) v_12 (mux (eq v_26 (expression.bv_nat 4 8)) v_13 (mux (eq v_26 (expression.bv_nat 4 7)) v_14 (mux (eq v_26 (expression.bv_nat 4 6)) v_15 (mux (eq v_26 (expression.bv_nat 4 5)) v_16 (mux (eq v_26 (expression.bv_nat 4 4)) v_17 (mux (eq v_26 (expression.bv_nat 4 3)) v_18 (mux (eq v_26 (expression.bv_nat 4 2)) v_19 (mux (eq v_26 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 48) (expression.bv_nat 8 0) (mux (eq v_27 (expression.bv_nat 4 15)) v_6 (mux (eq v_27 (expression.bv_nat 4 14)) v_7 (mux (eq v_27 (expression.bv_nat 4 13)) v_8 (mux (eq v_27 (expression.bv_nat 4 12)) v_9 (mux (eq v_27 (expression.bv_nat 4 11)) v_10 (mux (eq v_27 (expression.bv_nat 4 10)) v_11 (mux (eq v_27 (expression.bv_nat 4 9)) v_12 (mux (eq v_27 (expression.bv_nat 4 8)) v_13 (mux (eq v_27 (expression.bv_nat 4 7)) v_14 (mux (eq v_27 (expression.bv_nat 4 6)) v_15 (mux (eq v_27 (expression.bv_nat 4 5)) v_16 (mux (eq v_27 (expression.bv_nat 4 4)) v_17 (mux (eq v_27 (expression.bv_nat 4 3)) v_18 (mux (eq v_27 (expression.bv_nat 4 2)) v_19 (mux (eq v_27 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 56) (expression.bv_nat 8 0) (mux (eq v_28 (expression.bv_nat 4 15)) v_6 (mux (eq v_28 (expression.bv_nat 4 14)) v_7 (mux (eq v_28 (expression.bv_nat 4 13)) v_8 (mux (eq v_28 (expression.bv_nat 4 12)) v_9 (mux (eq v_28 (expression.bv_nat 4 11)) v_10 (mux (eq v_28 (expression.bv_nat 4 10)) v_11 (mux (eq v_28 (expression.bv_nat 4 9)) v_12 (mux (eq v_28 (expression.bv_nat 4 8)) v_13 (mux (eq v_28 (expression.bv_nat 4 7)) v_14 (mux (eq v_28 (expression.bv_nat 4 6)) v_15 (mux (eq v_28 (expression.bv_nat 4 5)) v_16 (mux (eq v_28 (expression.bv_nat 4 4)) v_17 (mux (eq v_28 (expression.bv_nat 4 3)) v_18 (mux (eq v_28 (expression.bv_nat 4 2)) v_19 (mux (eq v_28 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 64) (expression.bv_nat 8 0) (mux (eq v_29 (expression.bv_nat 4 15)) v_6 (mux (eq v_29 (expression.bv_nat 4 14)) v_7 (mux (eq v_29 (expression.bv_nat 4 13)) v_8 (mux (eq v_29 (expression.bv_nat 4 12)) v_9 (mux (eq v_29 (expression.bv_nat 4 11)) v_10 (mux (eq v_29 (expression.bv_nat 4 10)) v_11 (mux (eq v_29 (expression.bv_nat 4 9)) v_12 (mux (eq v_29 (expression.bv_nat 4 8)) v_13 (mux (eq v_29 (expression.bv_nat 4 7)) v_14 (mux (eq v_29 (expression.bv_nat 4 6)) v_15 (mux (eq v_29 (expression.bv_nat 4 5)) v_16 (mux (eq v_29 (expression.bv_nat 4 4)) v_17 (mux (eq v_29 (expression.bv_nat 4 3)) v_18 (mux (eq v_29 (expression.bv_nat 4 2)) v_19 (mux (eq v_29 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 72) (expression.bv_nat 8 0) (mux (eq v_30 (expression.bv_nat 4 15)) v_6 (mux (eq v_30 (expression.bv_nat 4 14)) v_7 (mux (eq v_30 (expression.bv_nat 4 13)) v_8 (mux (eq v_30 (expression.bv_nat 4 12)) v_9 (mux (eq v_30 (expression.bv_nat 4 11)) v_10 (mux (eq v_30 (expression.bv_nat 4 10)) v_11 (mux (eq v_30 (expression.bv_nat 4 9)) v_12 (mux (eq v_30 (expression.bv_nat 4 8)) v_13 (mux (eq v_30 (expression.bv_nat 4 7)) v_14 (mux (eq v_30 (expression.bv_nat 4 6)) v_15 (mux (eq v_30 (expression.bv_nat 4 5)) v_16 (mux (eq v_30 (expression.bv_nat 4 4)) v_17 (mux (eq v_30 (expression.bv_nat 4 3)) v_18 (mux (eq v_30 (expression.bv_nat 4 2)) v_19 (mux (eq v_30 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 80) (expression.bv_nat 8 0) (mux (eq v_31 (expression.bv_nat 4 15)) v_6 (mux (eq v_31 (expression.bv_nat 4 14)) v_7 (mux (eq v_31 (expression.bv_nat 4 13)) v_8 (mux (eq v_31 (expression.bv_nat 4 12)) v_9 (mux (eq v_31 (expression.bv_nat 4 11)) v_10 (mux (eq v_31 (expression.bv_nat 4 10)) v_11 (mux (eq v_31 (expression.bv_nat 4 9)) v_12 (mux (eq v_31 (expression.bv_nat 4 8)) v_13 (mux (eq v_31 (expression.bv_nat 4 7)) v_14 (mux (eq v_31 (expression.bv_nat 4 6)) v_15 (mux (eq v_31 (expression.bv_nat 4 5)) v_16 (mux (eq v_31 (expression.bv_nat 4 4)) v_17 (mux (eq v_31 (expression.bv_nat 4 3)) v_18 (mux (eq v_31 (expression.bv_nat 4 2)) v_19 (mux (eq v_31 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 88) (expression.bv_nat 8 0) (mux (eq v_32 (expression.bv_nat 4 15)) v_6 (mux (eq v_32 (expression.bv_nat 4 14)) v_7 (mux (eq v_32 (expression.bv_nat 4 13)) v_8 (mux (eq v_32 (expression.bv_nat 4 12)) v_9 (mux (eq v_32 (expression.bv_nat 4 11)) v_10 (mux (eq v_32 (expression.bv_nat 4 10)) v_11 (mux (eq v_32 (expression.bv_nat 4 9)) v_12 (mux (eq v_32 (expression.bv_nat 4 8)) v_13 (mux (eq v_32 (expression.bv_nat 4 7)) v_14 (mux (eq v_32 (expression.bv_nat 4 6)) v_15 (mux (eq v_32 (expression.bv_nat 4 5)) v_16 (mux (eq v_32 (expression.bv_nat 4 4)) v_17 (mux (eq v_32 (expression.bv_nat 4 3)) v_18 (mux (eq v_32 (expression.bv_nat 4 2)) v_19 (mux (eq v_32 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 96) (expression.bv_nat 8 0) (mux (eq v_33 (expression.bv_nat 4 15)) v_6 (mux (eq v_33 (expression.bv_nat 4 14)) v_7 (mux (eq v_33 (expression.bv_nat 4 13)) v_8 (mux (eq v_33 (expression.bv_nat 4 12)) v_9 (mux (eq v_33 (expression.bv_nat 4 11)) v_10 (mux (eq v_33 (expression.bv_nat 4 10)) v_11 (mux (eq v_33 (expression.bv_nat 4 9)) v_12 (mux (eq v_33 (expression.bv_nat 4 8)) v_13 (mux (eq v_33 (expression.bv_nat 4 7)) v_14 (mux (eq v_33 (expression.bv_nat 4 6)) v_15 (mux (eq v_33 (expression.bv_nat 4 5)) v_16 (mux (eq v_33 (expression.bv_nat 4 4)) v_17 (mux (eq v_33 (expression.bv_nat 4 3)) v_18 (mux (eq v_33 (expression.bv_nat 4 2)) v_19 (mux (eq v_33 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 104) (expression.bv_nat 8 0) (mux (eq v_34 (expression.bv_nat 4 15)) v_6 (mux (eq v_34 (expression.bv_nat 4 14)) v_7 (mux (eq v_34 (expression.bv_nat 4 13)) v_8 (mux (eq v_34 (expression.bv_nat 4 12)) v_9 (mux (eq v_34 (expression.bv_nat 4 11)) v_10 (mux (eq v_34 (expression.bv_nat 4 10)) v_11 (mux (eq v_34 (expression.bv_nat 4 9)) v_12 (mux (eq v_34 (expression.bv_nat 4 8)) v_13 (mux (eq v_34 (expression.bv_nat 4 7)) v_14 (mux (eq v_34 (expression.bv_nat 4 6)) v_15 (mux (eq v_34 (expression.bv_nat 4 5)) v_16 (mux (eq v_34 (expression.bv_nat 4 4)) v_17 (mux (eq v_34 (expression.bv_nat 4 3)) v_18 (mux (eq v_34 (expression.bv_nat 4 2)) v_19 (mux (eq v_34 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (concat (mux (isBitSet v_3 112) (expression.bv_nat 8 0) (mux (eq v_35 (expression.bv_nat 4 15)) v_6 (mux (eq v_35 (expression.bv_nat 4 14)) v_7 (mux (eq v_35 (expression.bv_nat 4 13)) v_8 (mux (eq v_35 (expression.bv_nat 4 12)) v_9 (mux (eq v_35 (expression.bv_nat 4 11)) v_10 (mux (eq v_35 (expression.bv_nat 4 10)) v_11 (mux (eq v_35 (expression.bv_nat 4 9)) v_12 (mux (eq v_35 (expression.bv_nat 4 8)) v_13 (mux (eq v_35 (expression.bv_nat 4 7)) v_14 (mux (eq v_35 (expression.bv_nat 4 6)) v_15 (mux (eq v_35 (expression.bv_nat 4 5)) v_16 (mux (eq v_35 (expression.bv_nat 4 4)) v_17 (mux (eq v_35 (expression.bv_nat 4 3)) v_18 (mux (eq v_35 (expression.bv_nat 4 2)) v_19 (mux (eq v_35 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))) (mux (isBitSet v_3 120) (expression.bv_nat 8 0) (mux (eq v_36 (expression.bv_nat 4 15)) v_6 (mux (eq v_36 (expression.bv_nat 4 14)) v_7 (mux (eq v_36 (expression.bv_nat 4 13)) v_8 (mux (eq v_36 (expression.bv_nat 4 12)) v_9 (mux (eq v_36 (expression.bv_nat 4 11)) v_10 (mux (eq v_36 (expression.bv_nat 4 10)) v_11 (mux (eq v_36 (expression.bv_nat 4 9)) v_12 (mux (eq v_36 (expression.bv_nat 4 8)) v_13 (mux (eq v_36 (expression.bv_nat 4 7)) v_14 (mux (eq v_36 (expression.bv_nat 4 6)) v_15 (mux (eq v_36 (expression.bv_nat 4 5)) v_16 (mux (eq v_36 (expression.bv_nat 4 4)) v_17 (mux (eq v_36 (expression.bv_nat 4 3)) v_18 (mux (eq v_36 (expression.bv_nat 4 2)) v_19 (mux (eq v_36 (expression.bv_nat 4 1)) v_20 v_21)))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- eval (extract v_2 4 8);
      v_4 <- getRegister xmm_1;
      v_5 <- eval (extract v_4 0 8);
      v_6 <- eval (extract v_4 8 16);
      v_7 <- eval (extract v_4 16 24);
      v_8 <- eval (extract v_4 24 32);
      v_9 <- eval (extract v_4 32 40);
      v_10 <- eval (extract v_4 40 48);
      v_11 <- eval (extract v_4 48 56);
      v_12 <- eval (extract v_4 56 64);
      v_13 <- eval (extract v_4 64 72);
      v_14 <- eval (extract v_4 72 80);
      v_15 <- eval (extract v_4 80 88);
      v_16 <- eval (extract v_4 88 96);
      v_17 <- eval (extract v_4 96 104);
      v_18 <- eval (extract v_4 104 112);
      v_19 <- eval (extract v_4 112 120);
      v_20 <- eval (extract v_4 120 128);
      v_21 <- eval (extract v_2 12 16);
      v_22 <- eval (extract v_2 20 24);
      v_23 <- eval (extract v_2 28 32);
      v_24 <- eval (extract v_2 36 40);
      v_25 <- eval (extract v_2 44 48);
      v_26 <- eval (extract v_2 52 56);
      v_27 <- eval (extract v_2 60 64);
      v_28 <- eval (extract v_2 68 72);
      v_29 <- eval (extract v_2 76 80);
      v_30 <- eval (extract v_2 84 88);
      v_31 <- eval (extract v_2 92 96);
      v_32 <- eval (extract v_2 100 104);
      v_33 <- eval (extract v_2 108 112);
      v_34 <- eval (extract v_2 116 120);
      v_35 <- eval (extract v_2 124 128);
      setRegister (lhs.of_reg xmm_1) (concat (mux (isBitSet v_2 0) (expression.bv_nat 8 0) (mux (eq v_3 (expression.bv_nat 4 15)) v_5 (mux (eq v_3 (expression.bv_nat 4 14)) v_6 (mux (eq v_3 (expression.bv_nat 4 13)) v_7 (mux (eq v_3 (expression.bv_nat 4 12)) v_8 (mux (eq v_3 (expression.bv_nat 4 11)) v_9 (mux (eq v_3 (expression.bv_nat 4 10)) v_10 (mux (eq v_3 (expression.bv_nat 4 9)) v_11 (mux (eq v_3 (expression.bv_nat 4 8)) v_12 (mux (eq v_3 (expression.bv_nat 4 7)) v_13 (mux (eq v_3 (expression.bv_nat 4 6)) v_14 (mux (eq v_3 (expression.bv_nat 4 5)) v_15 (mux (eq v_3 (expression.bv_nat 4 4)) v_16 (mux (eq v_3 (expression.bv_nat 4 3)) v_17 (mux (eq v_3 (expression.bv_nat 4 2)) v_18 (mux (eq v_3 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 8) (expression.bv_nat 8 0) (mux (eq v_21 (expression.bv_nat 4 15)) v_5 (mux (eq v_21 (expression.bv_nat 4 14)) v_6 (mux (eq v_21 (expression.bv_nat 4 13)) v_7 (mux (eq v_21 (expression.bv_nat 4 12)) v_8 (mux (eq v_21 (expression.bv_nat 4 11)) v_9 (mux (eq v_21 (expression.bv_nat 4 10)) v_10 (mux (eq v_21 (expression.bv_nat 4 9)) v_11 (mux (eq v_21 (expression.bv_nat 4 8)) v_12 (mux (eq v_21 (expression.bv_nat 4 7)) v_13 (mux (eq v_21 (expression.bv_nat 4 6)) v_14 (mux (eq v_21 (expression.bv_nat 4 5)) v_15 (mux (eq v_21 (expression.bv_nat 4 4)) v_16 (mux (eq v_21 (expression.bv_nat 4 3)) v_17 (mux (eq v_21 (expression.bv_nat 4 2)) v_18 (mux (eq v_21 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 16) (expression.bv_nat 8 0) (mux (eq v_22 (expression.bv_nat 4 15)) v_5 (mux (eq v_22 (expression.bv_nat 4 14)) v_6 (mux (eq v_22 (expression.bv_nat 4 13)) v_7 (mux (eq v_22 (expression.bv_nat 4 12)) v_8 (mux (eq v_22 (expression.bv_nat 4 11)) v_9 (mux (eq v_22 (expression.bv_nat 4 10)) v_10 (mux (eq v_22 (expression.bv_nat 4 9)) v_11 (mux (eq v_22 (expression.bv_nat 4 8)) v_12 (mux (eq v_22 (expression.bv_nat 4 7)) v_13 (mux (eq v_22 (expression.bv_nat 4 6)) v_14 (mux (eq v_22 (expression.bv_nat 4 5)) v_15 (mux (eq v_22 (expression.bv_nat 4 4)) v_16 (mux (eq v_22 (expression.bv_nat 4 3)) v_17 (mux (eq v_22 (expression.bv_nat 4 2)) v_18 (mux (eq v_22 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 24) (expression.bv_nat 8 0) (mux (eq v_23 (expression.bv_nat 4 15)) v_5 (mux (eq v_23 (expression.bv_nat 4 14)) v_6 (mux (eq v_23 (expression.bv_nat 4 13)) v_7 (mux (eq v_23 (expression.bv_nat 4 12)) v_8 (mux (eq v_23 (expression.bv_nat 4 11)) v_9 (mux (eq v_23 (expression.bv_nat 4 10)) v_10 (mux (eq v_23 (expression.bv_nat 4 9)) v_11 (mux (eq v_23 (expression.bv_nat 4 8)) v_12 (mux (eq v_23 (expression.bv_nat 4 7)) v_13 (mux (eq v_23 (expression.bv_nat 4 6)) v_14 (mux (eq v_23 (expression.bv_nat 4 5)) v_15 (mux (eq v_23 (expression.bv_nat 4 4)) v_16 (mux (eq v_23 (expression.bv_nat 4 3)) v_17 (mux (eq v_23 (expression.bv_nat 4 2)) v_18 (mux (eq v_23 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 32) (expression.bv_nat 8 0) (mux (eq v_24 (expression.bv_nat 4 15)) v_5 (mux (eq v_24 (expression.bv_nat 4 14)) v_6 (mux (eq v_24 (expression.bv_nat 4 13)) v_7 (mux (eq v_24 (expression.bv_nat 4 12)) v_8 (mux (eq v_24 (expression.bv_nat 4 11)) v_9 (mux (eq v_24 (expression.bv_nat 4 10)) v_10 (mux (eq v_24 (expression.bv_nat 4 9)) v_11 (mux (eq v_24 (expression.bv_nat 4 8)) v_12 (mux (eq v_24 (expression.bv_nat 4 7)) v_13 (mux (eq v_24 (expression.bv_nat 4 6)) v_14 (mux (eq v_24 (expression.bv_nat 4 5)) v_15 (mux (eq v_24 (expression.bv_nat 4 4)) v_16 (mux (eq v_24 (expression.bv_nat 4 3)) v_17 (mux (eq v_24 (expression.bv_nat 4 2)) v_18 (mux (eq v_24 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 40) (expression.bv_nat 8 0) (mux (eq v_25 (expression.bv_nat 4 15)) v_5 (mux (eq v_25 (expression.bv_nat 4 14)) v_6 (mux (eq v_25 (expression.bv_nat 4 13)) v_7 (mux (eq v_25 (expression.bv_nat 4 12)) v_8 (mux (eq v_25 (expression.bv_nat 4 11)) v_9 (mux (eq v_25 (expression.bv_nat 4 10)) v_10 (mux (eq v_25 (expression.bv_nat 4 9)) v_11 (mux (eq v_25 (expression.bv_nat 4 8)) v_12 (mux (eq v_25 (expression.bv_nat 4 7)) v_13 (mux (eq v_25 (expression.bv_nat 4 6)) v_14 (mux (eq v_25 (expression.bv_nat 4 5)) v_15 (mux (eq v_25 (expression.bv_nat 4 4)) v_16 (mux (eq v_25 (expression.bv_nat 4 3)) v_17 (mux (eq v_25 (expression.bv_nat 4 2)) v_18 (mux (eq v_25 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 48) (expression.bv_nat 8 0) (mux (eq v_26 (expression.bv_nat 4 15)) v_5 (mux (eq v_26 (expression.bv_nat 4 14)) v_6 (mux (eq v_26 (expression.bv_nat 4 13)) v_7 (mux (eq v_26 (expression.bv_nat 4 12)) v_8 (mux (eq v_26 (expression.bv_nat 4 11)) v_9 (mux (eq v_26 (expression.bv_nat 4 10)) v_10 (mux (eq v_26 (expression.bv_nat 4 9)) v_11 (mux (eq v_26 (expression.bv_nat 4 8)) v_12 (mux (eq v_26 (expression.bv_nat 4 7)) v_13 (mux (eq v_26 (expression.bv_nat 4 6)) v_14 (mux (eq v_26 (expression.bv_nat 4 5)) v_15 (mux (eq v_26 (expression.bv_nat 4 4)) v_16 (mux (eq v_26 (expression.bv_nat 4 3)) v_17 (mux (eq v_26 (expression.bv_nat 4 2)) v_18 (mux (eq v_26 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 56) (expression.bv_nat 8 0) (mux (eq v_27 (expression.bv_nat 4 15)) v_5 (mux (eq v_27 (expression.bv_nat 4 14)) v_6 (mux (eq v_27 (expression.bv_nat 4 13)) v_7 (mux (eq v_27 (expression.bv_nat 4 12)) v_8 (mux (eq v_27 (expression.bv_nat 4 11)) v_9 (mux (eq v_27 (expression.bv_nat 4 10)) v_10 (mux (eq v_27 (expression.bv_nat 4 9)) v_11 (mux (eq v_27 (expression.bv_nat 4 8)) v_12 (mux (eq v_27 (expression.bv_nat 4 7)) v_13 (mux (eq v_27 (expression.bv_nat 4 6)) v_14 (mux (eq v_27 (expression.bv_nat 4 5)) v_15 (mux (eq v_27 (expression.bv_nat 4 4)) v_16 (mux (eq v_27 (expression.bv_nat 4 3)) v_17 (mux (eq v_27 (expression.bv_nat 4 2)) v_18 (mux (eq v_27 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 64) (expression.bv_nat 8 0) (mux (eq v_28 (expression.bv_nat 4 15)) v_5 (mux (eq v_28 (expression.bv_nat 4 14)) v_6 (mux (eq v_28 (expression.bv_nat 4 13)) v_7 (mux (eq v_28 (expression.bv_nat 4 12)) v_8 (mux (eq v_28 (expression.bv_nat 4 11)) v_9 (mux (eq v_28 (expression.bv_nat 4 10)) v_10 (mux (eq v_28 (expression.bv_nat 4 9)) v_11 (mux (eq v_28 (expression.bv_nat 4 8)) v_12 (mux (eq v_28 (expression.bv_nat 4 7)) v_13 (mux (eq v_28 (expression.bv_nat 4 6)) v_14 (mux (eq v_28 (expression.bv_nat 4 5)) v_15 (mux (eq v_28 (expression.bv_nat 4 4)) v_16 (mux (eq v_28 (expression.bv_nat 4 3)) v_17 (mux (eq v_28 (expression.bv_nat 4 2)) v_18 (mux (eq v_28 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 72) (expression.bv_nat 8 0) (mux (eq v_29 (expression.bv_nat 4 15)) v_5 (mux (eq v_29 (expression.bv_nat 4 14)) v_6 (mux (eq v_29 (expression.bv_nat 4 13)) v_7 (mux (eq v_29 (expression.bv_nat 4 12)) v_8 (mux (eq v_29 (expression.bv_nat 4 11)) v_9 (mux (eq v_29 (expression.bv_nat 4 10)) v_10 (mux (eq v_29 (expression.bv_nat 4 9)) v_11 (mux (eq v_29 (expression.bv_nat 4 8)) v_12 (mux (eq v_29 (expression.bv_nat 4 7)) v_13 (mux (eq v_29 (expression.bv_nat 4 6)) v_14 (mux (eq v_29 (expression.bv_nat 4 5)) v_15 (mux (eq v_29 (expression.bv_nat 4 4)) v_16 (mux (eq v_29 (expression.bv_nat 4 3)) v_17 (mux (eq v_29 (expression.bv_nat 4 2)) v_18 (mux (eq v_29 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 80) (expression.bv_nat 8 0) (mux (eq v_30 (expression.bv_nat 4 15)) v_5 (mux (eq v_30 (expression.bv_nat 4 14)) v_6 (mux (eq v_30 (expression.bv_nat 4 13)) v_7 (mux (eq v_30 (expression.bv_nat 4 12)) v_8 (mux (eq v_30 (expression.bv_nat 4 11)) v_9 (mux (eq v_30 (expression.bv_nat 4 10)) v_10 (mux (eq v_30 (expression.bv_nat 4 9)) v_11 (mux (eq v_30 (expression.bv_nat 4 8)) v_12 (mux (eq v_30 (expression.bv_nat 4 7)) v_13 (mux (eq v_30 (expression.bv_nat 4 6)) v_14 (mux (eq v_30 (expression.bv_nat 4 5)) v_15 (mux (eq v_30 (expression.bv_nat 4 4)) v_16 (mux (eq v_30 (expression.bv_nat 4 3)) v_17 (mux (eq v_30 (expression.bv_nat 4 2)) v_18 (mux (eq v_30 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 88) (expression.bv_nat 8 0) (mux (eq v_31 (expression.bv_nat 4 15)) v_5 (mux (eq v_31 (expression.bv_nat 4 14)) v_6 (mux (eq v_31 (expression.bv_nat 4 13)) v_7 (mux (eq v_31 (expression.bv_nat 4 12)) v_8 (mux (eq v_31 (expression.bv_nat 4 11)) v_9 (mux (eq v_31 (expression.bv_nat 4 10)) v_10 (mux (eq v_31 (expression.bv_nat 4 9)) v_11 (mux (eq v_31 (expression.bv_nat 4 8)) v_12 (mux (eq v_31 (expression.bv_nat 4 7)) v_13 (mux (eq v_31 (expression.bv_nat 4 6)) v_14 (mux (eq v_31 (expression.bv_nat 4 5)) v_15 (mux (eq v_31 (expression.bv_nat 4 4)) v_16 (mux (eq v_31 (expression.bv_nat 4 3)) v_17 (mux (eq v_31 (expression.bv_nat 4 2)) v_18 (mux (eq v_31 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 96) (expression.bv_nat 8 0) (mux (eq v_32 (expression.bv_nat 4 15)) v_5 (mux (eq v_32 (expression.bv_nat 4 14)) v_6 (mux (eq v_32 (expression.bv_nat 4 13)) v_7 (mux (eq v_32 (expression.bv_nat 4 12)) v_8 (mux (eq v_32 (expression.bv_nat 4 11)) v_9 (mux (eq v_32 (expression.bv_nat 4 10)) v_10 (mux (eq v_32 (expression.bv_nat 4 9)) v_11 (mux (eq v_32 (expression.bv_nat 4 8)) v_12 (mux (eq v_32 (expression.bv_nat 4 7)) v_13 (mux (eq v_32 (expression.bv_nat 4 6)) v_14 (mux (eq v_32 (expression.bv_nat 4 5)) v_15 (mux (eq v_32 (expression.bv_nat 4 4)) v_16 (mux (eq v_32 (expression.bv_nat 4 3)) v_17 (mux (eq v_32 (expression.bv_nat 4 2)) v_18 (mux (eq v_32 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 104) (expression.bv_nat 8 0) (mux (eq v_33 (expression.bv_nat 4 15)) v_5 (mux (eq v_33 (expression.bv_nat 4 14)) v_6 (mux (eq v_33 (expression.bv_nat 4 13)) v_7 (mux (eq v_33 (expression.bv_nat 4 12)) v_8 (mux (eq v_33 (expression.bv_nat 4 11)) v_9 (mux (eq v_33 (expression.bv_nat 4 10)) v_10 (mux (eq v_33 (expression.bv_nat 4 9)) v_11 (mux (eq v_33 (expression.bv_nat 4 8)) v_12 (mux (eq v_33 (expression.bv_nat 4 7)) v_13 (mux (eq v_33 (expression.bv_nat 4 6)) v_14 (mux (eq v_33 (expression.bv_nat 4 5)) v_15 (mux (eq v_33 (expression.bv_nat 4 4)) v_16 (mux (eq v_33 (expression.bv_nat 4 3)) v_17 (mux (eq v_33 (expression.bv_nat 4 2)) v_18 (mux (eq v_33 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (concat (mux (isBitSet v_2 112) (expression.bv_nat 8 0) (mux (eq v_34 (expression.bv_nat 4 15)) v_5 (mux (eq v_34 (expression.bv_nat 4 14)) v_6 (mux (eq v_34 (expression.bv_nat 4 13)) v_7 (mux (eq v_34 (expression.bv_nat 4 12)) v_8 (mux (eq v_34 (expression.bv_nat 4 11)) v_9 (mux (eq v_34 (expression.bv_nat 4 10)) v_10 (mux (eq v_34 (expression.bv_nat 4 9)) v_11 (mux (eq v_34 (expression.bv_nat 4 8)) v_12 (mux (eq v_34 (expression.bv_nat 4 7)) v_13 (mux (eq v_34 (expression.bv_nat 4 6)) v_14 (mux (eq v_34 (expression.bv_nat 4 5)) v_15 (mux (eq v_34 (expression.bv_nat 4 4)) v_16 (mux (eq v_34 (expression.bv_nat 4 3)) v_17 (mux (eq v_34 (expression.bv_nat 4 2)) v_18 (mux (eq v_34 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))) (mux (isBitSet v_2 120) (expression.bv_nat 8 0) (mux (eq v_35 (expression.bv_nat 4 15)) v_5 (mux (eq v_35 (expression.bv_nat 4 14)) v_6 (mux (eq v_35 (expression.bv_nat 4 13)) v_7 (mux (eq v_35 (expression.bv_nat 4 12)) v_8 (mux (eq v_35 (expression.bv_nat 4 11)) v_9 (mux (eq v_35 (expression.bv_nat 4 10)) v_10 (mux (eq v_35 (expression.bv_nat 4 9)) v_11 (mux (eq v_35 (expression.bv_nat 4 8)) v_12 (mux (eq v_35 (expression.bv_nat 4 7)) v_13 (mux (eq v_35 (expression.bv_nat 4 6)) v_14 (mux (eq v_35 (expression.bv_nat 4 5)) v_15 (mux (eq v_35 (expression.bv_nat 4 4)) v_16 (mux (eq v_35 (expression.bv_nat 4 3)) v_17 (mux (eq v_35 (expression.bv_nat 4 2)) v_18 (mux (eq v_35 (expression.bv_nat 4 1)) v_19 v_20)))))))))))))))))))))))))))))));
      pure ()
    pat_end

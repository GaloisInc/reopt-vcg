def vpmovmskb : instruction :=
  definst "vpmovmskb" $ do
    pattern fun (xmm_0 : reg (bv 128)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 8 9);
      (v_5 : expression (bv 1)) <- eval (extract v_2 16 17);
      (v_6 : expression (bv 1)) <- eval (extract v_2 24 25);
      (v_7 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_8 : expression (bv 1)) <- eval (extract v_2 40 41);
      (v_9 : expression (bv 1)) <- eval (extract v_2 48 49);
      (v_10 : expression (bv 1)) <- eval (extract v_2 56 57);
      (v_11 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_12 : expression (bv 1)) <- eval (extract v_2 72 73);
      (v_13 : expression (bv 1)) <- eval (extract v_2 80 81);
      (v_14 : expression (bv 1)) <- eval (extract v_2 88 89);
      (v_15 : expression (bv 1)) <- eval (extract v_2 96 97);
      (v_16 : expression (bv 1)) <- eval (extract v_2 104 105);
      (v_17 : expression (bv 1)) <- eval (extract v_2 112 113);
      (v_18 : expression (bv 1)) <- eval (extract v_2 120 121);
      setRegister (lhs.of_reg r32_1) (concat (expression.bv_nat 16 0) (concat v_3 (concat v_4 (concat v_5 (concat v_6 (concat v_7 (concat v_8 (concat v_9 (concat v_10 (concat v_11 (concat v_12 (concat v_13 (concat v_14 (concat v_15 (concat v_16 (concat v_17 v_18))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 8 9);
      (v_5 : expression (bv 1)) <- eval (extract v_2 16 17);
      (v_6 : expression (bv 1)) <- eval (extract v_2 24 25);
      (v_7 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_8 : expression (bv 1)) <- eval (extract v_2 40 41);
      (v_9 : expression (bv 1)) <- eval (extract v_2 48 49);
      (v_10 : expression (bv 1)) <- eval (extract v_2 56 57);
      (v_11 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_12 : expression (bv 1)) <- eval (extract v_2 72 73);
      (v_13 : expression (bv 1)) <- eval (extract v_2 80 81);
      (v_14 : expression (bv 1)) <- eval (extract v_2 88 89);
      (v_15 : expression (bv 1)) <- eval (extract v_2 96 97);
      (v_16 : expression (bv 1)) <- eval (extract v_2 104 105);
      (v_17 : expression (bv 1)) <- eval (extract v_2 112 113);
      (v_18 : expression (bv 1)) <- eval (extract v_2 120 121);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 48 0) (concat v_3 (concat v_4 (concat v_5 (concat v_6 (concat v_7 (concat v_8 (concat v_9 (concat v_10 (concat v_11 (concat v_12 (concat v_13 (concat v_14 (concat v_15 (concat v_16 (concat v_17 v_18))))))))))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 8 9);
      (v_5 : expression (bv 1)) <- eval (extract v_2 16 17);
      (v_6 : expression (bv 1)) <- eval (extract v_2 24 25);
      (v_7 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_8 : expression (bv 1)) <- eval (extract v_2 40 41);
      (v_9 : expression (bv 1)) <- eval (extract v_2 48 49);
      (v_10 : expression (bv 1)) <- eval (extract v_2 56 57);
      (v_11 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_12 : expression (bv 1)) <- eval (extract v_2 72 73);
      (v_13 : expression (bv 1)) <- eval (extract v_2 80 81);
      (v_14 : expression (bv 1)) <- eval (extract v_2 88 89);
      (v_15 : expression (bv 1)) <- eval (extract v_2 96 97);
      (v_16 : expression (bv 1)) <- eval (extract v_2 104 105);
      (v_17 : expression (bv 1)) <- eval (extract v_2 112 113);
      (v_18 : expression (bv 1)) <- eval (extract v_2 120 121);
      (v_19 : expression (bv 1)) <- eval (extract v_2 128 129);
      (v_20 : expression (bv 1)) <- eval (extract v_2 136 137);
      (v_21 : expression (bv 1)) <- eval (extract v_2 144 145);
      (v_22 : expression (bv 1)) <- eval (extract v_2 152 153);
      (v_23 : expression (bv 1)) <- eval (extract v_2 160 161);
      (v_24 : expression (bv 1)) <- eval (extract v_2 168 169);
      (v_25 : expression (bv 1)) <- eval (extract v_2 176 177);
      (v_26 : expression (bv 1)) <- eval (extract v_2 184 185);
      (v_27 : expression (bv 1)) <- eval (extract v_2 192 193);
      (v_28 : expression (bv 1)) <- eval (extract v_2 200 201);
      (v_29 : expression (bv 1)) <- eval (extract v_2 208 209);
      (v_30 : expression (bv 1)) <- eval (extract v_2 216 217);
      (v_31 : expression (bv 1)) <- eval (extract v_2 224 225);
      (v_32 : expression (bv 1)) <- eval (extract v_2 232 233);
      (v_33 : expression (bv 1)) <- eval (extract v_2 240 241);
      (v_34 : expression (bv 1)) <- eval (extract v_2 248 249);
      setRegister (lhs.of_reg r32_1) (concat v_3 (concat v_4 (concat v_5 (concat v_6 (concat v_7 (concat v_8 (concat v_9 (concat v_10 (concat v_11 (concat v_12 (concat v_13 (concat v_14 (concat v_15 (concat v_16 (concat v_17 (concat v_18 (concat v_19 (concat v_20 (concat v_21 (concat v_22 (concat v_23 (concat v_24 (concat v_25 (concat v_26 (concat v_27 (concat v_28 (concat v_29 (concat v_30 (concat v_31 (concat v_32 (concat v_33 v_34)))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      (v_4 : expression (bv 1)) <- eval (extract v_2 8 9);
      (v_5 : expression (bv 1)) <- eval (extract v_2 16 17);
      (v_6 : expression (bv 1)) <- eval (extract v_2 24 25);
      (v_7 : expression (bv 1)) <- eval (extract v_2 32 33);
      (v_8 : expression (bv 1)) <- eval (extract v_2 40 41);
      (v_9 : expression (bv 1)) <- eval (extract v_2 48 49);
      (v_10 : expression (bv 1)) <- eval (extract v_2 56 57);
      (v_11 : expression (bv 1)) <- eval (extract v_2 64 65);
      (v_12 : expression (bv 1)) <- eval (extract v_2 72 73);
      (v_13 : expression (bv 1)) <- eval (extract v_2 80 81);
      (v_14 : expression (bv 1)) <- eval (extract v_2 88 89);
      (v_15 : expression (bv 1)) <- eval (extract v_2 96 97);
      (v_16 : expression (bv 1)) <- eval (extract v_2 104 105);
      (v_17 : expression (bv 1)) <- eval (extract v_2 112 113);
      (v_18 : expression (bv 1)) <- eval (extract v_2 120 121);
      (v_19 : expression (bv 1)) <- eval (extract v_2 128 129);
      (v_20 : expression (bv 1)) <- eval (extract v_2 136 137);
      (v_21 : expression (bv 1)) <- eval (extract v_2 144 145);
      (v_22 : expression (bv 1)) <- eval (extract v_2 152 153);
      (v_23 : expression (bv 1)) <- eval (extract v_2 160 161);
      (v_24 : expression (bv 1)) <- eval (extract v_2 168 169);
      (v_25 : expression (bv 1)) <- eval (extract v_2 176 177);
      (v_26 : expression (bv 1)) <- eval (extract v_2 184 185);
      (v_27 : expression (bv 1)) <- eval (extract v_2 192 193);
      (v_28 : expression (bv 1)) <- eval (extract v_2 200 201);
      (v_29 : expression (bv 1)) <- eval (extract v_2 208 209);
      (v_30 : expression (bv 1)) <- eval (extract v_2 216 217);
      (v_31 : expression (bv 1)) <- eval (extract v_2 224 225);
      (v_32 : expression (bv 1)) <- eval (extract v_2 232 233);
      (v_33 : expression (bv 1)) <- eval (extract v_2 240 241);
      (v_34 : expression (bv 1)) <- eval (extract v_2 248 249);
      setRegister (lhs.of_reg r64_1) (concat (expression.bv_nat 32 0) (concat v_3 (concat v_4 (concat v_5 (concat v_6 (concat v_7 (concat v_8 (concat v_9 (concat v_10 (concat v_11 (concat v_12 (concat v_13 (concat v_14 (concat v_15 (concat v_16 (concat v_17 (concat v_18 (concat v_19 (concat v_20 (concat v_21 (concat v_22 (concat v_23 (concat v_24 (concat v_25 (concat v_26 (concat v_27 (concat v_28 (concat v_29 (concat v_30 (concat v_31 (concat v_32 (concat v_33 v_34))))))))))))))))))))))))))))))));
      pure ()
    pat_end

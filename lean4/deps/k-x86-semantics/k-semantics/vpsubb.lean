def vpsubb : instruction :=
  definst "vpsubb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 8)) <- eval (extract v_6 0 8);
      (v_8 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_6 8 16);
      (v_10 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_11 : expression (bv 8)) <- eval (extract v_6 16 24);
      (v_12 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_6 24 32);
      (v_14 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_15 : expression (bv 8)) <- eval (extract v_6 32 40);
      (v_16 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_17 : expression (bv 8)) <- eval (extract v_6 40 48);
      (v_18 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_19 : expression (bv 8)) <- eval (extract v_6 48 56);
      (v_20 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_21 : expression (bv 8)) <- eval (extract v_6 56 64);
      (v_22 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_23 : expression (bv 8)) <- eval (extract v_6 64 72);
      (v_24 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_25 : expression (bv 8)) <- eval (extract v_6 72 80);
      (v_26 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_27 : expression (bv 8)) <- eval (extract v_6 80 88);
      (v_28 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_29 : expression (bv 8)) <- eval (extract v_6 88 96);
      (v_30 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_31 : expression (bv 8)) <- eval (extract v_6 96 104);
      (v_32 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_33 : expression (bv 8)) <- eval (extract v_6 104 112);
      (v_34 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_35 : expression (bv 8)) <- eval (extract v_6 112 120);
      (v_36 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_37 : expression (bv 8)) <- eval (extract v_6 120 128);
      setRegister (lhs.of_reg xmm_2) (concat (sub v_4 v_7) (concat (sub v_8 v_9) (concat (sub v_10 v_11) (concat (sub v_12 v_13) (concat (sub v_14 v_15) (concat (sub v_16 v_17) (concat (sub v_18 v_19) (concat (sub v_20 v_21) (concat (sub v_22 v_23) (concat (sub v_24 v_25) (concat (sub v_26 v_27) (concat (sub v_28 v_29) (concat (sub v_30 v_31) (concat (sub v_32 v_33) (concat (sub v_34 v_35) (sub v_36 v_37))))))))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 8)) <- eval (extract v_6 0 8);
      (v_8 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_6 8 16);
      (v_10 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_11 : expression (bv 8)) <- eval (extract v_6 16 24);
      (v_12 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_6 24 32);
      (v_14 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_15 : expression (bv 8)) <- eval (extract v_6 32 40);
      (v_16 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_17 : expression (bv 8)) <- eval (extract v_6 40 48);
      (v_18 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_19 : expression (bv 8)) <- eval (extract v_6 48 56);
      (v_20 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_21 : expression (bv 8)) <- eval (extract v_6 56 64);
      (v_22 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_23 : expression (bv 8)) <- eval (extract v_6 64 72);
      (v_24 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_25 : expression (bv 8)) <- eval (extract v_6 72 80);
      (v_26 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_27 : expression (bv 8)) <- eval (extract v_6 80 88);
      (v_28 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_29 : expression (bv 8)) <- eval (extract v_6 88 96);
      (v_30 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_31 : expression (bv 8)) <- eval (extract v_6 96 104);
      (v_32 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_33 : expression (bv 8)) <- eval (extract v_6 104 112);
      (v_34 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_35 : expression (bv 8)) <- eval (extract v_6 112 120);
      (v_36 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_37 : expression (bv 8)) <- eval (extract v_6 120 128);
      (v_38 : expression (bv 8)) <- eval (extract v_3 128 136);
      (v_39 : expression (bv 8)) <- eval (extract v_6 128 136);
      (v_40 : expression (bv 8)) <- eval (extract v_3 136 144);
      (v_41 : expression (bv 8)) <- eval (extract v_6 136 144);
      (v_42 : expression (bv 8)) <- eval (extract v_3 144 152);
      (v_43 : expression (bv 8)) <- eval (extract v_6 144 152);
      (v_44 : expression (bv 8)) <- eval (extract v_3 152 160);
      (v_45 : expression (bv 8)) <- eval (extract v_6 152 160);
      (v_46 : expression (bv 8)) <- eval (extract v_3 160 168);
      (v_47 : expression (bv 8)) <- eval (extract v_6 160 168);
      (v_48 : expression (bv 8)) <- eval (extract v_3 168 176);
      (v_49 : expression (bv 8)) <- eval (extract v_6 168 176);
      (v_50 : expression (bv 8)) <- eval (extract v_3 176 184);
      (v_51 : expression (bv 8)) <- eval (extract v_6 176 184);
      (v_52 : expression (bv 8)) <- eval (extract v_3 184 192);
      (v_53 : expression (bv 8)) <- eval (extract v_6 184 192);
      (v_54 : expression (bv 8)) <- eval (extract v_3 192 200);
      (v_55 : expression (bv 8)) <- eval (extract v_6 192 200);
      (v_56 : expression (bv 8)) <- eval (extract v_3 200 208);
      (v_57 : expression (bv 8)) <- eval (extract v_6 200 208);
      (v_58 : expression (bv 8)) <- eval (extract v_3 208 216);
      (v_59 : expression (bv 8)) <- eval (extract v_6 208 216);
      (v_60 : expression (bv 8)) <- eval (extract v_3 216 224);
      (v_61 : expression (bv 8)) <- eval (extract v_6 216 224);
      (v_62 : expression (bv 8)) <- eval (extract v_3 224 232);
      (v_63 : expression (bv 8)) <- eval (extract v_6 224 232);
      (v_64 : expression (bv 8)) <- eval (extract v_3 232 240);
      (v_65 : expression (bv 8)) <- eval (extract v_6 232 240);
      (v_66 : expression (bv 8)) <- eval (extract v_3 240 248);
      (v_67 : expression (bv 8)) <- eval (extract v_6 240 248);
      (v_68 : expression (bv 8)) <- eval (extract v_3 248 256);
      (v_69 : expression (bv 8)) <- eval (extract v_6 248 256);
      setRegister (lhs.of_reg ymm_2) (concat (sub v_4 v_7) (concat (sub v_8 v_9) (concat (sub v_10 v_11) (concat (sub v_12 v_13) (concat (sub v_14 v_15) (concat (sub v_16 v_17) (concat (sub v_18 v_19) (concat (sub v_20 v_21) (concat (sub v_22 v_23) (concat (sub v_24 v_25) (concat (sub v_26 v_27) (concat (sub v_28 v_29) (concat (sub v_30 v_31) (concat (sub v_32 v_33) (concat (sub v_34 v_35) (concat (sub v_36 v_37) (concat (sub v_38 v_39) (concat (sub v_40 v_41) (concat (sub v_42 v_43) (concat (sub v_44 v_45) (concat (sub v_46 v_47) (concat (sub v_48 v_49) (concat (sub v_50 v_51) (concat (sub v_52 v_53) (concat (sub v_54 v_55) (concat (sub v_56 v_57) (concat (sub v_58 v_59) (concat (sub v_60 v_61) (concat (sub v_62 v_63) (concat (sub v_64 v_65) (concat (sub v_66 v_67) (sub v_68 v_69))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      (v_7 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_5 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_5 16 24);
      (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_14 : expression (bv 8)) <- eval (extract v_5 32 40);
      (v_15 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_16 : expression (bv 8)) <- eval (extract v_5 40 48);
      (v_17 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_18 : expression (bv 8)) <- eval (extract v_5 48 56);
      (v_19 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_20 : expression (bv 8)) <- eval (extract v_5 56 64);
      (v_21 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_22 : expression (bv 8)) <- eval (extract v_5 64 72);
      (v_23 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_24 : expression (bv 8)) <- eval (extract v_5 72 80);
      (v_25 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_26 : expression (bv 8)) <- eval (extract v_5 80 88);
      (v_27 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_28 : expression (bv 8)) <- eval (extract v_5 88 96);
      (v_29 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_30 : expression (bv 8)) <- eval (extract v_5 96 104);
      (v_31 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_32 : expression (bv 8)) <- eval (extract v_5 104 112);
      (v_33 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_34 : expression (bv 8)) <- eval (extract v_5 112 120);
      (v_35 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_36 : expression (bv 8)) <- eval (extract v_5 120 128);
      setRegister (lhs.of_reg xmm_2) (concat (sub v_4 v_6) (concat (sub v_7 v_8) (concat (sub v_9 v_10) (concat (sub v_11 v_12) (concat (sub v_13 v_14) (concat (sub v_15 v_16) (concat (sub v_17 v_18) (concat (sub v_19 v_20) (concat (sub v_21 v_22) (concat (sub v_23 v_24) (concat (sub v_25 v_26) (concat (sub v_27 v_28) (concat (sub v_29 v_30) (concat (sub v_31 v_32) (concat (sub v_33 v_34) (sub v_35 v_36))))))))))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      (v_7 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_5 8 16);
      (v_9 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_10 : expression (bv 8)) <- eval (extract v_5 16 24);
      (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_14 : expression (bv 8)) <- eval (extract v_5 32 40);
      (v_15 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_16 : expression (bv 8)) <- eval (extract v_5 40 48);
      (v_17 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_18 : expression (bv 8)) <- eval (extract v_5 48 56);
      (v_19 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_20 : expression (bv 8)) <- eval (extract v_5 56 64);
      (v_21 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_22 : expression (bv 8)) <- eval (extract v_5 64 72);
      (v_23 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_24 : expression (bv 8)) <- eval (extract v_5 72 80);
      (v_25 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_26 : expression (bv 8)) <- eval (extract v_5 80 88);
      (v_27 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_28 : expression (bv 8)) <- eval (extract v_5 88 96);
      (v_29 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_30 : expression (bv 8)) <- eval (extract v_5 96 104);
      (v_31 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_32 : expression (bv 8)) <- eval (extract v_5 104 112);
      (v_33 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_34 : expression (bv 8)) <- eval (extract v_5 112 120);
      (v_35 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_36 : expression (bv 8)) <- eval (extract v_5 120 128);
      (v_37 : expression (bv 8)) <- eval (extract v_3 128 136);
      (v_38 : expression (bv 8)) <- eval (extract v_5 128 136);
      (v_39 : expression (bv 8)) <- eval (extract v_3 136 144);
      (v_40 : expression (bv 8)) <- eval (extract v_5 136 144);
      (v_41 : expression (bv 8)) <- eval (extract v_3 144 152);
      (v_42 : expression (bv 8)) <- eval (extract v_5 144 152);
      (v_43 : expression (bv 8)) <- eval (extract v_3 152 160);
      (v_44 : expression (bv 8)) <- eval (extract v_5 152 160);
      (v_45 : expression (bv 8)) <- eval (extract v_3 160 168);
      (v_46 : expression (bv 8)) <- eval (extract v_5 160 168);
      (v_47 : expression (bv 8)) <- eval (extract v_3 168 176);
      (v_48 : expression (bv 8)) <- eval (extract v_5 168 176);
      (v_49 : expression (bv 8)) <- eval (extract v_3 176 184);
      (v_50 : expression (bv 8)) <- eval (extract v_5 176 184);
      (v_51 : expression (bv 8)) <- eval (extract v_3 184 192);
      (v_52 : expression (bv 8)) <- eval (extract v_5 184 192);
      (v_53 : expression (bv 8)) <- eval (extract v_3 192 200);
      (v_54 : expression (bv 8)) <- eval (extract v_5 192 200);
      (v_55 : expression (bv 8)) <- eval (extract v_3 200 208);
      (v_56 : expression (bv 8)) <- eval (extract v_5 200 208);
      (v_57 : expression (bv 8)) <- eval (extract v_3 208 216);
      (v_58 : expression (bv 8)) <- eval (extract v_5 208 216);
      (v_59 : expression (bv 8)) <- eval (extract v_3 216 224);
      (v_60 : expression (bv 8)) <- eval (extract v_5 216 224);
      (v_61 : expression (bv 8)) <- eval (extract v_3 224 232);
      (v_62 : expression (bv 8)) <- eval (extract v_5 224 232);
      (v_63 : expression (bv 8)) <- eval (extract v_3 232 240);
      (v_64 : expression (bv 8)) <- eval (extract v_5 232 240);
      (v_65 : expression (bv 8)) <- eval (extract v_3 240 248);
      (v_66 : expression (bv 8)) <- eval (extract v_5 240 248);
      (v_67 : expression (bv 8)) <- eval (extract v_3 248 256);
      (v_68 : expression (bv 8)) <- eval (extract v_5 248 256);
      setRegister (lhs.of_reg ymm_2) (concat (sub v_4 v_6) (concat (sub v_7 v_8) (concat (sub v_9 v_10) (concat (sub v_11 v_12) (concat (sub v_13 v_14) (concat (sub v_15 v_16) (concat (sub v_17 v_18) (concat (sub v_19 v_20) (concat (sub v_21 v_22) (concat (sub v_23 v_24) (concat (sub v_25 v_26) (concat (sub v_27 v_28) (concat (sub v_29 v_30) (concat (sub v_31 v_32) (concat (sub v_33 v_34) (concat (sub v_35 v_36) (concat (sub v_37 v_38) (concat (sub v_39 v_40) (concat (sub v_41 v_42) (concat (sub v_43 v_44) (concat (sub v_45 v_46) (concat (sub v_47 v_48) (concat (sub v_49 v_50) (concat (sub v_51 v_52) (concat (sub v_53 v_54) (concat (sub v_55 v_56) (concat (sub v_57 v_58) (concat (sub v_59 v_60) (concat (sub v_61 v_62) (concat (sub v_63 v_64) (concat (sub v_65 v_66) (sub v_67 v_68))))))))))))))))))))))))))))))));
      pure ()
    pat_end

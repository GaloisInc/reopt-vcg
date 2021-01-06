def vpmaxub : instruction :=
  definst "vpmaxub" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 8)) <- eval (extract v_6 0 8);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_9 : expression (bv 8)) <- eval (extract v_6 8 16);
      let (v_10 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_11 : expression (bv 8)) <- eval (extract v_6 16 24);
      let (v_12 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_13 : expression (bv 8)) <- eval (extract v_6 24 32);
      let (v_14 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_15 : expression (bv 8)) <- eval (extract v_6 32 40);
      let (v_16 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_17 : expression (bv 8)) <- eval (extract v_6 40 48);
      let (v_18 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_19 : expression (bv 8)) <- eval (extract v_6 48 56);
      let (v_20 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_21 : expression (bv 8)) <- eval (extract v_6 56 64);
      let (v_22 : expression (bv 8)) <- eval (extract v_3 64 72);
      let (v_23 : expression (bv 8)) <- eval (extract v_6 64 72);
      let (v_24 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_25 : expression (bv 8)) <- eval (extract v_6 72 80);
      let (v_26 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_27 : expression (bv 8)) <- eval (extract v_6 80 88);
      let (v_28 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_29 : expression (bv 8)) <- eval (extract v_6 88 96);
      let (v_30 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_31 : expression (bv 8)) <- eval (extract v_6 96 104);
      let (v_32 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_33 : expression (bv 8)) <- eval (extract v_6 104 112);
      let (v_34 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_35 : expression (bv 8)) <- eval (extract v_6 112 120);
      let (v_36 : expression (bv 8)) <- eval (extract v_3 120 128);
      let (v_37 : expression (bv 8)) <- eval (extract v_6 120 128);
      let v_38 <- eval (concat (mux (ugt v_34 v_35) v_34 v_35) (mux (ugt v_36 v_37) v_36 v_37));
      let v_39 <- eval (concat (mux (ugt v_32 v_33) v_32 v_33) v_38);
      let v_40 <- eval (concat (mux (ugt v_30 v_31) v_30 v_31) v_39);
      let v_41 <- eval (concat (mux (ugt v_28 v_29) v_28 v_29) v_40);
      let v_42 <- eval (concat (mux (ugt v_26 v_27) v_26 v_27) v_41);
      let v_43 <- eval (concat (mux (ugt v_24 v_25) v_24 v_25) v_42);
      let v_44 <- eval (concat (mux (ugt v_22 v_23) v_22 v_23) v_43);
      let v_45 <- eval (concat (mux (ugt v_20 v_21) v_20 v_21) v_44);
      let v_46 <- eval (concat (mux (ugt v_18 v_19) v_18 v_19) v_45);
      let v_47 <- eval (concat (mux (ugt v_16 v_17) v_16 v_17) v_46);
      let v_48 <- eval (concat (mux (ugt v_14 v_15) v_14 v_15) v_47);
      let v_49 <- eval (concat (mux (ugt v_12 v_13) v_12 v_13) v_48);
      let v_50 <- eval (concat (mux (ugt v_10 v_11) v_10 v_11) v_49);
      let v_51 <- eval (concat (mux (ugt v_8 v_9) v_8 v_9) v_50);
      let v_52 <- eval (concat (mux (ugt v_4 v_7) v_4 v_7) v_51);
      setRegister (lhs.of_reg xmm_2) v_52;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 32;
      let (v_7 : expression (bv 8)) <- eval (extract v_6 0 8);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_9 : expression (bv 8)) <- eval (extract v_6 8 16);
      let (v_10 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_11 : expression (bv 8)) <- eval (extract v_6 16 24);
      let (v_12 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_13 : expression (bv 8)) <- eval (extract v_6 24 32);
      let (v_14 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_15 : expression (bv 8)) <- eval (extract v_6 32 40);
      let (v_16 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_17 : expression (bv 8)) <- eval (extract v_6 40 48);
      let (v_18 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_19 : expression (bv 8)) <- eval (extract v_6 48 56);
      let (v_20 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_21 : expression (bv 8)) <- eval (extract v_6 56 64);
      let (v_22 : expression (bv 8)) <- eval (extract v_3 64 72);
      let (v_23 : expression (bv 8)) <- eval (extract v_6 64 72);
      let (v_24 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_25 : expression (bv 8)) <- eval (extract v_6 72 80);
      let (v_26 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_27 : expression (bv 8)) <- eval (extract v_6 80 88);
      let (v_28 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_29 : expression (bv 8)) <- eval (extract v_6 88 96);
      let (v_30 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_31 : expression (bv 8)) <- eval (extract v_6 96 104);
      let (v_32 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_33 : expression (bv 8)) <- eval (extract v_6 104 112);
      let (v_34 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_35 : expression (bv 8)) <- eval (extract v_6 112 120);
      let (v_36 : expression (bv 8)) <- eval (extract v_3 120 128);
      let (v_37 : expression (bv 8)) <- eval (extract v_6 120 128);
      let (v_38 : expression (bv 8)) <- eval (extract v_3 128 136);
      let (v_39 : expression (bv 8)) <- eval (extract v_6 128 136);
      let (v_40 : expression (bv 8)) <- eval (extract v_3 136 144);
      let (v_41 : expression (bv 8)) <- eval (extract v_6 136 144);
      let (v_42 : expression (bv 8)) <- eval (extract v_3 144 152);
      let (v_43 : expression (bv 8)) <- eval (extract v_6 144 152);
      let (v_44 : expression (bv 8)) <- eval (extract v_3 152 160);
      let (v_45 : expression (bv 8)) <- eval (extract v_6 152 160);
      let (v_46 : expression (bv 8)) <- eval (extract v_3 160 168);
      let (v_47 : expression (bv 8)) <- eval (extract v_6 160 168);
      let (v_48 : expression (bv 8)) <- eval (extract v_3 168 176);
      let (v_49 : expression (bv 8)) <- eval (extract v_6 168 176);
      let (v_50 : expression (bv 8)) <- eval (extract v_3 176 184);
      let (v_51 : expression (bv 8)) <- eval (extract v_6 176 184);
      let (v_52 : expression (bv 8)) <- eval (extract v_3 184 192);
      let (v_53 : expression (bv 8)) <- eval (extract v_6 184 192);
      let (v_54 : expression (bv 8)) <- eval (extract v_3 192 200);
      let (v_55 : expression (bv 8)) <- eval (extract v_6 192 200);
      let (v_56 : expression (bv 8)) <- eval (extract v_3 200 208);
      let (v_57 : expression (bv 8)) <- eval (extract v_6 200 208);
      let (v_58 : expression (bv 8)) <- eval (extract v_3 208 216);
      let (v_59 : expression (bv 8)) <- eval (extract v_6 208 216);
      let (v_60 : expression (bv 8)) <- eval (extract v_3 216 224);
      let (v_61 : expression (bv 8)) <- eval (extract v_6 216 224);
      let (v_62 : expression (bv 8)) <- eval (extract v_3 224 232);
      let (v_63 : expression (bv 8)) <- eval (extract v_6 224 232);
      let (v_64 : expression (bv 8)) <- eval (extract v_3 232 240);
      let (v_65 : expression (bv 8)) <- eval (extract v_6 232 240);
      let (v_66 : expression (bv 8)) <- eval (extract v_3 240 248);
      let (v_67 : expression (bv 8)) <- eval (extract v_6 240 248);
      let (v_68 : expression (bv 8)) <- eval (extract v_3 248 256);
      let (v_69 : expression (bv 8)) <- eval (extract v_6 248 256);
      let v_70 <- eval (concat (mux (ugt v_66 v_67) v_66 v_67) (mux (ugt v_68 v_69) v_68 v_69));
      let v_71 <- eval (concat (mux (ugt v_64 v_65) v_64 v_65) v_70);
      let v_72 <- eval (concat (mux (ugt v_62 v_63) v_62 v_63) v_71);
      let v_73 <- eval (concat (mux (ugt v_60 v_61) v_60 v_61) v_72);
      let v_74 <- eval (concat (mux (ugt v_58 v_59) v_58 v_59) v_73);
      let v_75 <- eval (concat (mux (ugt v_56 v_57) v_56 v_57) v_74);
      let v_76 <- eval (concat (mux (ugt v_54 v_55) v_54 v_55) v_75);
      let v_77 <- eval (concat (mux (ugt v_52 v_53) v_52 v_53) v_76);
      let v_78 <- eval (concat (mux (ugt v_50 v_51) v_50 v_51) v_77);
      let v_79 <- eval (concat (mux (ugt v_48 v_49) v_48 v_49) v_78);
      let v_80 <- eval (concat (mux (ugt v_46 v_47) v_46 v_47) v_79);
      let v_81 <- eval (concat (mux (ugt v_44 v_45) v_44 v_45) v_80);
      let v_82 <- eval (concat (mux (ugt v_42 v_43) v_42 v_43) v_81);
      let v_83 <- eval (concat (mux (ugt v_40 v_41) v_40 v_41) v_82);
      let v_84 <- eval (concat (mux (ugt v_38 v_39) v_38 v_39) v_83);
      let v_85 <- eval (concat (mux (ugt v_36 v_37) v_36 v_37) v_84);
      let v_86 <- eval (concat (mux (ugt v_34 v_35) v_34 v_35) v_85);
      let v_87 <- eval (concat (mux (ugt v_32 v_33) v_32 v_33) v_86);
      let v_88 <- eval (concat (mux (ugt v_30 v_31) v_30 v_31) v_87);
      let v_89 <- eval (concat (mux (ugt v_28 v_29) v_28 v_29) v_88);
      let v_90 <- eval (concat (mux (ugt v_26 v_27) v_26 v_27) v_89);
      let v_91 <- eval (concat (mux (ugt v_24 v_25) v_24 v_25) v_90);
      let v_92 <- eval (concat (mux (ugt v_22 v_23) v_22 v_23) v_91);
      let v_93 <- eval (concat (mux (ugt v_20 v_21) v_20 v_21) v_92);
      let v_94 <- eval (concat (mux (ugt v_18 v_19) v_18 v_19) v_93);
      let v_95 <- eval (concat (mux (ugt v_16 v_17) v_16 v_17) v_94);
      let v_96 <- eval (concat (mux (ugt v_14 v_15) v_14 v_15) v_95);
      let v_97 <- eval (concat (mux (ugt v_12 v_13) v_12 v_13) v_96);
      let v_98 <- eval (concat (mux (ugt v_10 v_11) v_10 v_11) v_97);
      let v_99 <- eval (concat (mux (ugt v_8 v_9) v_8 v_9) v_98);
      let v_100 <- eval (concat (mux (ugt v_4 v_7) v_4 v_7) v_99);
      setRegister (lhs.of_reg ymm_2) v_100;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_8 : expression (bv 8)) <- eval (extract v_5 8 16);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_10 : expression (bv 8)) <- eval (extract v_5 16 24);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      let (v_13 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_14 : expression (bv 8)) <- eval (extract v_5 32 40);
      let (v_15 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_16 : expression (bv 8)) <- eval (extract v_5 40 48);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_18 : expression (bv 8)) <- eval (extract v_5 48 56);
      let (v_19 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_20 : expression (bv 8)) <- eval (extract v_5 56 64);
      let (v_21 : expression (bv 8)) <- eval (extract v_3 64 72);
      let (v_22 : expression (bv 8)) <- eval (extract v_5 64 72);
      let (v_23 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_24 : expression (bv 8)) <- eval (extract v_5 72 80);
      let (v_25 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_26 : expression (bv 8)) <- eval (extract v_5 80 88);
      let (v_27 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_28 : expression (bv 8)) <- eval (extract v_5 88 96);
      let (v_29 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_30 : expression (bv 8)) <- eval (extract v_5 96 104);
      let (v_31 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_32 : expression (bv 8)) <- eval (extract v_5 104 112);
      let (v_33 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_34 : expression (bv 8)) <- eval (extract v_5 112 120);
      let (v_35 : expression (bv 8)) <- eval (extract v_3 120 128);
      let (v_36 : expression (bv 8)) <- eval (extract v_5 120 128);
      let v_37 <- eval (concat (mux (ugt v_33 v_34) v_33 v_34) (mux (ugt v_35 v_36) v_35 v_36));
      let v_38 <- eval (concat (mux (ugt v_31 v_32) v_31 v_32) v_37);
      let v_39 <- eval (concat (mux (ugt v_29 v_30) v_29 v_30) v_38);
      let v_40 <- eval (concat (mux (ugt v_27 v_28) v_27 v_28) v_39);
      let v_41 <- eval (concat (mux (ugt v_25 v_26) v_25 v_26) v_40);
      let v_42 <- eval (concat (mux (ugt v_23 v_24) v_23 v_24) v_41);
      let v_43 <- eval (concat (mux (ugt v_21 v_22) v_21 v_22) v_42);
      let v_44 <- eval (concat (mux (ugt v_19 v_20) v_19 v_20) v_43);
      let v_45 <- eval (concat (mux (ugt v_17 v_18) v_17 v_18) v_44);
      let v_46 <- eval (concat (mux (ugt v_15 v_16) v_15 v_16) v_45);
      let v_47 <- eval (concat (mux (ugt v_13 v_14) v_13 v_14) v_46);
      let v_48 <- eval (concat (mux (ugt v_11 v_12) v_11 v_12) v_47);
      let v_49 <- eval (concat (mux (ugt v_9 v_10) v_9 v_10) v_48);
      let v_50 <- eval (concat (mux (ugt v_7 v_8) v_7 v_8) v_49);
      let v_51 <- eval (concat (mux (ugt v_4 v_6) v_4 v_6) v_50);
      setRegister (lhs.of_reg xmm_2) v_51;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      let v_5 <- getRegister (lhs.of_reg ymm_0);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      let (v_7 : expression (bv 8)) <- eval (extract v_3 8 16);
      let (v_8 : expression (bv 8)) <- eval (extract v_5 8 16);
      let (v_9 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_10 : expression (bv 8)) <- eval (extract v_5 16 24);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      let (v_13 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_14 : expression (bv 8)) <- eval (extract v_5 32 40);
      let (v_15 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_16 : expression (bv 8)) <- eval (extract v_5 40 48);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_18 : expression (bv 8)) <- eval (extract v_5 48 56);
      let (v_19 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_20 : expression (bv 8)) <- eval (extract v_5 56 64);
      let (v_21 : expression (bv 8)) <- eval (extract v_3 64 72);
      let (v_22 : expression (bv 8)) <- eval (extract v_5 64 72);
      let (v_23 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_24 : expression (bv 8)) <- eval (extract v_5 72 80);
      let (v_25 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_26 : expression (bv 8)) <- eval (extract v_5 80 88);
      let (v_27 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_28 : expression (bv 8)) <- eval (extract v_5 88 96);
      let (v_29 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_30 : expression (bv 8)) <- eval (extract v_5 96 104);
      let (v_31 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_32 : expression (bv 8)) <- eval (extract v_5 104 112);
      let (v_33 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_34 : expression (bv 8)) <- eval (extract v_5 112 120);
      let (v_35 : expression (bv 8)) <- eval (extract v_3 120 128);
      let (v_36 : expression (bv 8)) <- eval (extract v_5 120 128);
      let (v_37 : expression (bv 8)) <- eval (extract v_3 128 136);
      let (v_38 : expression (bv 8)) <- eval (extract v_5 128 136);
      let (v_39 : expression (bv 8)) <- eval (extract v_3 136 144);
      let (v_40 : expression (bv 8)) <- eval (extract v_5 136 144);
      let (v_41 : expression (bv 8)) <- eval (extract v_3 144 152);
      let (v_42 : expression (bv 8)) <- eval (extract v_5 144 152);
      let (v_43 : expression (bv 8)) <- eval (extract v_3 152 160);
      let (v_44 : expression (bv 8)) <- eval (extract v_5 152 160);
      let (v_45 : expression (bv 8)) <- eval (extract v_3 160 168);
      let (v_46 : expression (bv 8)) <- eval (extract v_5 160 168);
      let (v_47 : expression (bv 8)) <- eval (extract v_3 168 176);
      let (v_48 : expression (bv 8)) <- eval (extract v_5 168 176);
      let (v_49 : expression (bv 8)) <- eval (extract v_3 176 184);
      let (v_50 : expression (bv 8)) <- eval (extract v_5 176 184);
      let (v_51 : expression (bv 8)) <- eval (extract v_3 184 192);
      let (v_52 : expression (bv 8)) <- eval (extract v_5 184 192);
      let (v_53 : expression (bv 8)) <- eval (extract v_3 192 200);
      let (v_54 : expression (bv 8)) <- eval (extract v_5 192 200);
      let (v_55 : expression (bv 8)) <- eval (extract v_3 200 208);
      let (v_56 : expression (bv 8)) <- eval (extract v_5 200 208);
      let (v_57 : expression (bv 8)) <- eval (extract v_3 208 216);
      let (v_58 : expression (bv 8)) <- eval (extract v_5 208 216);
      let (v_59 : expression (bv 8)) <- eval (extract v_3 216 224);
      let (v_60 : expression (bv 8)) <- eval (extract v_5 216 224);
      let (v_61 : expression (bv 8)) <- eval (extract v_3 224 232);
      let (v_62 : expression (bv 8)) <- eval (extract v_5 224 232);
      let (v_63 : expression (bv 8)) <- eval (extract v_3 232 240);
      let (v_64 : expression (bv 8)) <- eval (extract v_5 232 240);
      let (v_65 : expression (bv 8)) <- eval (extract v_3 240 248);
      let (v_66 : expression (bv 8)) <- eval (extract v_5 240 248);
      let (v_67 : expression (bv 8)) <- eval (extract v_3 248 256);
      let (v_68 : expression (bv 8)) <- eval (extract v_5 248 256);
      let v_69 <- eval (concat (mux (ugt v_65 v_66) v_65 v_66) (mux (ugt v_67 v_68) v_67 v_68));
      let v_70 <- eval (concat (mux (ugt v_63 v_64) v_63 v_64) v_69);
      let v_71 <- eval (concat (mux (ugt v_61 v_62) v_61 v_62) v_70);
      let v_72 <- eval (concat (mux (ugt v_59 v_60) v_59 v_60) v_71);
      let v_73 <- eval (concat (mux (ugt v_57 v_58) v_57 v_58) v_72);
      let v_74 <- eval (concat (mux (ugt v_55 v_56) v_55 v_56) v_73);
      let v_75 <- eval (concat (mux (ugt v_53 v_54) v_53 v_54) v_74);
      let v_76 <- eval (concat (mux (ugt v_51 v_52) v_51 v_52) v_75);
      let v_77 <- eval (concat (mux (ugt v_49 v_50) v_49 v_50) v_76);
      let v_78 <- eval (concat (mux (ugt v_47 v_48) v_47 v_48) v_77);
      let v_79 <- eval (concat (mux (ugt v_45 v_46) v_45 v_46) v_78);
      let v_80 <- eval (concat (mux (ugt v_43 v_44) v_43 v_44) v_79);
      let v_81 <- eval (concat (mux (ugt v_41 v_42) v_41 v_42) v_80);
      let v_82 <- eval (concat (mux (ugt v_39 v_40) v_39 v_40) v_81);
      let v_83 <- eval (concat (mux (ugt v_37 v_38) v_37 v_38) v_82);
      let v_84 <- eval (concat (mux (ugt v_35 v_36) v_35 v_36) v_83);
      let v_85 <- eval (concat (mux (ugt v_33 v_34) v_33 v_34) v_84);
      let v_86 <- eval (concat (mux (ugt v_31 v_32) v_31 v_32) v_85);
      let v_87 <- eval (concat (mux (ugt v_29 v_30) v_29 v_30) v_86);
      let v_88 <- eval (concat (mux (ugt v_27 v_28) v_27 v_28) v_87);
      let v_89 <- eval (concat (mux (ugt v_25 v_26) v_25 v_26) v_88);
      let v_90 <- eval (concat (mux (ugt v_23 v_24) v_23 v_24) v_89);
      let v_91 <- eval (concat (mux (ugt v_21 v_22) v_21 v_22) v_90);
      let v_92 <- eval (concat (mux (ugt v_19 v_20) v_19 v_20) v_91);
      let v_93 <- eval (concat (mux (ugt v_17 v_18) v_17 v_18) v_92);
      let v_94 <- eval (concat (mux (ugt v_15 v_16) v_15 v_16) v_93);
      let v_95 <- eval (concat (mux (ugt v_13 v_14) v_13 v_14) v_94);
      let v_96 <- eval (concat (mux (ugt v_11 v_12) v_11 v_12) v_95);
      let v_97 <- eval (concat (mux (ugt v_9 v_10) v_9 v_10) v_96);
      let v_98 <- eval (concat (mux (ugt v_7 v_8) v_7 v_8) v_97);
      let v_99 <- eval (concat (mux (ugt v_4 v_6) v_4 v_6) v_98);
      setRegister (lhs.of_reg ymm_2) v_99;
      pure ()
     action

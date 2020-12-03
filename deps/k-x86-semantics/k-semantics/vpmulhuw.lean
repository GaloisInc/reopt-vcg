def vpmulhuw : instruction :=
  definst "vpmulhuw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (concat (expression.bv_nat 16 0) v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 16)) <- eval (extract v_7 0 16);
      let v_9 <- eval (concat (expression.bv_nat 16 0) v_8);
      let (v_10 : expression (bv 16)) <- eval (extract (mul v_5 v_9) 0 16);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_12 <- eval (concat (expression.bv_nat 16 0) v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_7 16 32);
      let v_14 <- eval (concat (expression.bv_nat 16 0) v_13);
      let (v_15 : expression (bv 16)) <- eval (extract (mul v_12 v_14) 0 16);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_17 <- eval (concat (expression.bv_nat 16 0) v_16);
      let (v_18 : expression (bv 16)) <- eval (extract v_7 32 48);
      let v_19 <- eval (concat (expression.bv_nat 16 0) v_18);
      let (v_20 : expression (bv 16)) <- eval (extract (mul v_17 v_19) 0 16);
      let (v_21 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_22 <- eval (concat (expression.bv_nat 16 0) v_21);
      let (v_23 : expression (bv 16)) <- eval (extract v_7 48 64);
      let v_24 <- eval (concat (expression.bv_nat 16 0) v_23);
      let (v_25 : expression (bv 16)) <- eval (extract (mul v_22 v_24) 0 16);
      let (v_26 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_27 <- eval (concat (expression.bv_nat 16 0) v_26);
      let (v_28 : expression (bv 16)) <- eval (extract v_7 64 80);
      let v_29 <- eval (concat (expression.bv_nat 16 0) v_28);
      let (v_30 : expression (bv 16)) <- eval (extract (mul v_27 v_29) 0 16);
      let (v_31 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_32 <- eval (concat (expression.bv_nat 16 0) v_31);
      let (v_33 : expression (bv 16)) <- eval (extract v_7 80 96);
      let v_34 <- eval (concat (expression.bv_nat 16 0) v_33);
      let (v_35 : expression (bv 16)) <- eval (extract (mul v_32 v_34) 0 16);
      let (v_36 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_37 <- eval (concat (expression.bv_nat 16 0) v_36);
      let (v_38 : expression (bv 16)) <- eval (extract v_7 96 112);
      let v_39 <- eval (concat (expression.bv_nat 16 0) v_38);
      let (v_40 : expression (bv 16)) <- eval (extract (mul v_37 v_39) 0 16);
      let (v_41 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_42 <- eval (concat (expression.bv_nat 16 0) v_41);
      let (v_43 : expression (bv 16)) <- eval (extract v_7 112 128);
      let v_44 <- eval (concat (expression.bv_nat 16 0) v_43);
      let (v_45 : expression (bv 16)) <- eval (extract (mul v_42 v_44) 0 16);
      let v_46 <- eval (concat v_40 v_45);
      let v_47 <- eval (concat v_35 v_46);
      let v_48 <- eval (concat v_30 v_47);
      let v_49 <- eval (concat v_25 v_48);
      let v_50 <- eval (concat v_20 v_49);
      let v_51 <- eval (concat v_15 v_50);
      let v_52 <- eval (concat v_10 v_51);
      setRegister (lhs.of_reg xmm_2) v_52;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (concat (expression.bv_nat 16 0) v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 32;
      let (v_8 : expression (bv 16)) <- eval (extract v_7 0 16);
      let v_9 <- eval (concat (expression.bv_nat 16 0) v_8);
      let (v_10 : expression (bv 16)) <- eval (extract (mul v_5 v_9) 0 16);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_12 <- eval (concat (expression.bv_nat 16 0) v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_7 16 32);
      let v_14 <- eval (concat (expression.bv_nat 16 0) v_13);
      let (v_15 : expression (bv 16)) <- eval (extract (mul v_12 v_14) 0 16);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_17 <- eval (concat (expression.bv_nat 16 0) v_16);
      let (v_18 : expression (bv 16)) <- eval (extract v_7 32 48);
      let v_19 <- eval (concat (expression.bv_nat 16 0) v_18);
      let (v_20 : expression (bv 16)) <- eval (extract (mul v_17 v_19) 0 16);
      let (v_21 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_22 <- eval (concat (expression.bv_nat 16 0) v_21);
      let (v_23 : expression (bv 16)) <- eval (extract v_7 48 64);
      let v_24 <- eval (concat (expression.bv_nat 16 0) v_23);
      let (v_25 : expression (bv 16)) <- eval (extract (mul v_22 v_24) 0 16);
      let (v_26 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_27 <- eval (concat (expression.bv_nat 16 0) v_26);
      let (v_28 : expression (bv 16)) <- eval (extract v_7 64 80);
      let v_29 <- eval (concat (expression.bv_nat 16 0) v_28);
      let (v_30 : expression (bv 16)) <- eval (extract (mul v_27 v_29) 0 16);
      let (v_31 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_32 <- eval (concat (expression.bv_nat 16 0) v_31);
      let (v_33 : expression (bv 16)) <- eval (extract v_7 80 96);
      let v_34 <- eval (concat (expression.bv_nat 16 0) v_33);
      let (v_35 : expression (bv 16)) <- eval (extract (mul v_32 v_34) 0 16);
      let (v_36 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_37 <- eval (concat (expression.bv_nat 16 0) v_36);
      let (v_38 : expression (bv 16)) <- eval (extract v_7 96 112);
      let v_39 <- eval (concat (expression.bv_nat 16 0) v_38);
      let (v_40 : expression (bv 16)) <- eval (extract (mul v_37 v_39) 0 16);
      let (v_41 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_42 <- eval (concat (expression.bv_nat 16 0) v_41);
      let (v_43 : expression (bv 16)) <- eval (extract v_7 112 128);
      let v_44 <- eval (concat (expression.bv_nat 16 0) v_43);
      let (v_45 : expression (bv 16)) <- eval (extract (mul v_42 v_44) 0 16);
      let (v_46 : expression (bv 16)) <- eval (extract v_3 128 144);
      let v_47 <- eval (concat (expression.bv_nat 16 0) v_46);
      let (v_48 : expression (bv 16)) <- eval (extract v_7 128 144);
      let v_49 <- eval (concat (expression.bv_nat 16 0) v_48);
      let (v_50 : expression (bv 16)) <- eval (extract (mul v_47 v_49) 0 16);
      let (v_51 : expression (bv 16)) <- eval (extract v_3 144 160);
      let v_52 <- eval (concat (expression.bv_nat 16 0) v_51);
      let (v_53 : expression (bv 16)) <- eval (extract v_7 144 160);
      let v_54 <- eval (concat (expression.bv_nat 16 0) v_53);
      let (v_55 : expression (bv 16)) <- eval (extract (mul v_52 v_54) 0 16);
      let (v_56 : expression (bv 16)) <- eval (extract v_3 160 176);
      let v_57 <- eval (concat (expression.bv_nat 16 0) v_56);
      let (v_58 : expression (bv 16)) <- eval (extract v_7 160 176);
      let v_59 <- eval (concat (expression.bv_nat 16 0) v_58);
      let (v_60 : expression (bv 16)) <- eval (extract (mul v_57 v_59) 0 16);
      let (v_61 : expression (bv 16)) <- eval (extract v_3 176 192);
      let v_62 <- eval (concat (expression.bv_nat 16 0) v_61);
      let (v_63 : expression (bv 16)) <- eval (extract v_7 176 192);
      let v_64 <- eval (concat (expression.bv_nat 16 0) v_63);
      let (v_65 : expression (bv 16)) <- eval (extract (mul v_62 v_64) 0 16);
      let (v_66 : expression (bv 16)) <- eval (extract v_3 192 208);
      let v_67 <- eval (concat (expression.bv_nat 16 0) v_66);
      let (v_68 : expression (bv 16)) <- eval (extract v_7 192 208);
      let v_69 <- eval (concat (expression.bv_nat 16 0) v_68);
      let (v_70 : expression (bv 16)) <- eval (extract (mul v_67 v_69) 0 16);
      let (v_71 : expression (bv 16)) <- eval (extract v_3 208 224);
      let v_72 <- eval (concat (expression.bv_nat 16 0) v_71);
      let (v_73 : expression (bv 16)) <- eval (extract v_7 208 224);
      let v_74 <- eval (concat (expression.bv_nat 16 0) v_73);
      let (v_75 : expression (bv 16)) <- eval (extract (mul v_72 v_74) 0 16);
      let (v_76 : expression (bv 16)) <- eval (extract v_3 224 240);
      let v_77 <- eval (concat (expression.bv_nat 16 0) v_76);
      let (v_78 : expression (bv 16)) <- eval (extract v_7 224 240);
      let v_79 <- eval (concat (expression.bv_nat 16 0) v_78);
      let (v_80 : expression (bv 16)) <- eval (extract (mul v_77 v_79) 0 16);
      let (v_81 : expression (bv 16)) <- eval (extract v_3 240 256);
      let v_82 <- eval (concat (expression.bv_nat 16 0) v_81);
      let (v_83 : expression (bv 16)) <- eval (extract v_7 240 256);
      let v_84 <- eval (concat (expression.bv_nat 16 0) v_83);
      let (v_85 : expression (bv 16)) <- eval (extract (mul v_82 v_84) 0 16);
      let v_86 <- eval (concat v_80 v_85);
      let v_87 <- eval (concat v_75 v_86);
      let v_88 <- eval (concat v_70 v_87);
      let v_89 <- eval (concat v_65 v_88);
      let v_90 <- eval (concat v_60 v_89);
      let v_91 <- eval (concat v_55 v_90);
      let v_92 <- eval (concat v_50 v_91);
      let v_93 <- eval (concat v_45 v_92);
      let v_94 <- eval (concat v_40 v_93);
      let v_95 <- eval (concat v_35 v_94);
      let v_96 <- eval (concat v_30 v_95);
      let v_97 <- eval (concat v_25 v_96);
      let v_98 <- eval (concat v_20 v_97);
      let v_99 <- eval (concat v_15 v_98);
      let v_100 <- eval (concat v_10 v_99);
      setRegister (lhs.of_reg ymm_2) v_100;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (concat (expression.bv_nat 16 0) v_4);
      let v_6 <- getRegister (lhs.of_reg xmm_0);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let v_8 <- eval (concat (expression.bv_nat 16 0) v_7);
      let (v_9 : expression (bv 16)) <- eval (extract (mul v_5 v_8) 0 16);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_11 <- eval (concat (expression.bv_nat 16 0) v_10);
      let (v_12 : expression (bv 16)) <- eval (extract v_6 16 32);
      let v_13 <- eval (concat (expression.bv_nat 16 0) v_12);
      let (v_14 : expression (bv 16)) <- eval (extract (mul v_11 v_13) 0 16);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_16 <- eval (concat (expression.bv_nat 16 0) v_15);
      let (v_17 : expression (bv 16)) <- eval (extract v_6 32 48);
      let v_18 <- eval (concat (expression.bv_nat 16 0) v_17);
      let (v_19 : expression (bv 16)) <- eval (extract (mul v_16 v_18) 0 16);
      let (v_20 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_21 <- eval (concat (expression.bv_nat 16 0) v_20);
      let (v_22 : expression (bv 16)) <- eval (extract v_6 48 64);
      let v_23 <- eval (concat (expression.bv_nat 16 0) v_22);
      let (v_24 : expression (bv 16)) <- eval (extract (mul v_21 v_23) 0 16);
      let (v_25 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_26 <- eval (concat (expression.bv_nat 16 0) v_25);
      let (v_27 : expression (bv 16)) <- eval (extract v_6 64 80);
      let v_28 <- eval (concat (expression.bv_nat 16 0) v_27);
      let (v_29 : expression (bv 16)) <- eval (extract (mul v_26 v_28) 0 16);
      let (v_30 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_31 <- eval (concat (expression.bv_nat 16 0) v_30);
      let (v_32 : expression (bv 16)) <- eval (extract v_6 80 96);
      let v_33 <- eval (concat (expression.bv_nat 16 0) v_32);
      let (v_34 : expression (bv 16)) <- eval (extract (mul v_31 v_33) 0 16);
      let (v_35 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_36 <- eval (concat (expression.bv_nat 16 0) v_35);
      let (v_37 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_38 <- eval (concat (expression.bv_nat 16 0) v_37);
      let (v_39 : expression (bv 16)) <- eval (extract (mul v_36 v_38) 0 16);
      let (v_40 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_41 <- eval (concat (expression.bv_nat 16 0) v_40);
      let (v_42 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_43 <- eval (concat (expression.bv_nat 16 0) v_42);
      let (v_44 : expression (bv 16)) <- eval (extract (mul v_41 v_43) 0 16);
      let v_45 <- eval (concat v_39 v_44);
      let v_46 <- eval (concat v_34 v_45);
      let v_47 <- eval (concat v_29 v_46);
      let v_48 <- eval (concat v_24 v_47);
      let v_49 <- eval (concat v_19 v_48);
      let v_50 <- eval (concat v_14 v_49);
      let v_51 <- eval (concat v_9 v_50);
      setRegister (lhs.of_reg xmm_2) v_51;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (concat (expression.bv_nat 16 0) v_4);
      let v_6 <- getRegister (lhs.of_reg ymm_0);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let v_8 <- eval (concat (expression.bv_nat 16 0) v_7);
      let (v_9 : expression (bv 16)) <- eval (extract (mul v_5 v_8) 0 16);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_11 <- eval (concat (expression.bv_nat 16 0) v_10);
      let (v_12 : expression (bv 16)) <- eval (extract v_6 16 32);
      let v_13 <- eval (concat (expression.bv_nat 16 0) v_12);
      let (v_14 : expression (bv 16)) <- eval (extract (mul v_11 v_13) 0 16);
      let (v_15 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_16 <- eval (concat (expression.bv_nat 16 0) v_15);
      let (v_17 : expression (bv 16)) <- eval (extract v_6 32 48);
      let v_18 <- eval (concat (expression.bv_nat 16 0) v_17);
      let (v_19 : expression (bv 16)) <- eval (extract (mul v_16 v_18) 0 16);
      let (v_20 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_21 <- eval (concat (expression.bv_nat 16 0) v_20);
      let (v_22 : expression (bv 16)) <- eval (extract v_6 48 64);
      let v_23 <- eval (concat (expression.bv_nat 16 0) v_22);
      let (v_24 : expression (bv 16)) <- eval (extract (mul v_21 v_23) 0 16);
      let (v_25 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_26 <- eval (concat (expression.bv_nat 16 0) v_25);
      let (v_27 : expression (bv 16)) <- eval (extract v_6 64 80);
      let v_28 <- eval (concat (expression.bv_nat 16 0) v_27);
      let (v_29 : expression (bv 16)) <- eval (extract (mul v_26 v_28) 0 16);
      let (v_30 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_31 <- eval (concat (expression.bv_nat 16 0) v_30);
      let (v_32 : expression (bv 16)) <- eval (extract v_6 80 96);
      let v_33 <- eval (concat (expression.bv_nat 16 0) v_32);
      let (v_34 : expression (bv 16)) <- eval (extract (mul v_31 v_33) 0 16);
      let (v_35 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_36 <- eval (concat (expression.bv_nat 16 0) v_35);
      let (v_37 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_38 <- eval (concat (expression.bv_nat 16 0) v_37);
      let (v_39 : expression (bv 16)) <- eval (extract (mul v_36 v_38) 0 16);
      let (v_40 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_41 <- eval (concat (expression.bv_nat 16 0) v_40);
      let (v_42 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_43 <- eval (concat (expression.bv_nat 16 0) v_42);
      let (v_44 : expression (bv 16)) <- eval (extract (mul v_41 v_43) 0 16);
      let (v_45 : expression (bv 16)) <- eval (extract v_3 128 144);
      let v_46 <- eval (concat (expression.bv_nat 16 0) v_45);
      let (v_47 : expression (bv 16)) <- eval (extract v_6 128 144);
      let v_48 <- eval (concat (expression.bv_nat 16 0) v_47);
      let (v_49 : expression (bv 16)) <- eval (extract (mul v_46 v_48) 0 16);
      let (v_50 : expression (bv 16)) <- eval (extract v_3 144 160);
      let v_51 <- eval (concat (expression.bv_nat 16 0) v_50);
      let (v_52 : expression (bv 16)) <- eval (extract v_6 144 160);
      let v_53 <- eval (concat (expression.bv_nat 16 0) v_52);
      let (v_54 : expression (bv 16)) <- eval (extract (mul v_51 v_53) 0 16);
      let (v_55 : expression (bv 16)) <- eval (extract v_3 160 176);
      let v_56 <- eval (concat (expression.bv_nat 16 0) v_55);
      let (v_57 : expression (bv 16)) <- eval (extract v_6 160 176);
      let v_58 <- eval (concat (expression.bv_nat 16 0) v_57);
      let (v_59 : expression (bv 16)) <- eval (extract (mul v_56 v_58) 0 16);
      let (v_60 : expression (bv 16)) <- eval (extract v_3 176 192);
      let v_61 <- eval (concat (expression.bv_nat 16 0) v_60);
      let (v_62 : expression (bv 16)) <- eval (extract v_6 176 192);
      let v_63 <- eval (concat (expression.bv_nat 16 0) v_62);
      let (v_64 : expression (bv 16)) <- eval (extract (mul v_61 v_63) 0 16);
      let (v_65 : expression (bv 16)) <- eval (extract v_3 192 208);
      let v_66 <- eval (concat (expression.bv_nat 16 0) v_65);
      let (v_67 : expression (bv 16)) <- eval (extract v_6 192 208);
      let v_68 <- eval (concat (expression.bv_nat 16 0) v_67);
      let (v_69 : expression (bv 16)) <- eval (extract (mul v_66 v_68) 0 16);
      let (v_70 : expression (bv 16)) <- eval (extract v_3 208 224);
      let v_71 <- eval (concat (expression.bv_nat 16 0) v_70);
      let (v_72 : expression (bv 16)) <- eval (extract v_6 208 224);
      let v_73 <- eval (concat (expression.bv_nat 16 0) v_72);
      let (v_74 : expression (bv 16)) <- eval (extract (mul v_71 v_73) 0 16);
      let (v_75 : expression (bv 16)) <- eval (extract v_3 224 240);
      let v_76 <- eval (concat (expression.bv_nat 16 0) v_75);
      let (v_77 : expression (bv 16)) <- eval (extract v_6 224 240);
      let v_78 <- eval (concat (expression.bv_nat 16 0) v_77);
      let (v_79 : expression (bv 16)) <- eval (extract (mul v_76 v_78) 0 16);
      let (v_80 : expression (bv 16)) <- eval (extract v_3 240 256);
      let v_81 <- eval (concat (expression.bv_nat 16 0) v_80);
      let (v_82 : expression (bv 16)) <- eval (extract v_6 240 256);
      let v_83 <- eval (concat (expression.bv_nat 16 0) v_82);
      let (v_84 : expression (bv 16)) <- eval (extract (mul v_81 v_83) 0 16);
      let v_85 <- eval (concat v_79 v_84);
      let v_86 <- eval (concat v_74 v_85);
      let v_87 <- eval (concat v_69 v_86);
      let v_88 <- eval (concat v_64 v_87);
      let v_89 <- eval (concat v_59 v_88);
      let v_90 <- eval (concat v_54 v_89);
      let v_91 <- eval (concat v_49 v_90);
      let v_92 <- eval (concat v_44 v_91);
      let v_93 <- eval (concat v_39 v_92);
      let v_94 <- eval (concat v_34 v_93);
      let v_95 <- eval (concat v_29 v_94);
      let v_96 <- eval (concat v_24 v_95);
      let v_97 <- eval (concat v_19 v_96);
      let v_98 <- eval (concat v_14 v_97);
      let v_99 <- eval (concat v_9 v_98);
      setRegister (lhs.of_reg ymm_2) v_99;
      pure ()
     action

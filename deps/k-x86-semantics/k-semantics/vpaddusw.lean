def vpaddusw : instruction :=
  definst "vpaddusw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 16)) <- eval (extract v_7 0 16);
      let v_9 <- eval (concat (expression.bv_nat 1 0) v_8);
      let v_10 <- eval (add v_5 v_9);
      let (v_11 : expression (bv 16)) <- eval (extract v_10 1 17);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_13 <- eval (concat (expression.bv_nat 1 0) v_12);
      let (v_14 : expression (bv 16)) <- eval (extract v_7 16 32);
      let v_15 <- eval (concat (expression.bv_nat 1 0) v_14);
      let v_16 <- eval (add v_13 v_15);
      let (v_17 : expression (bv 16)) <- eval (extract v_16 1 17);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_19 <- eval (concat (expression.bv_nat 1 0) v_18);
      let (v_20 : expression (bv 16)) <- eval (extract v_7 32 48);
      let v_21 <- eval (concat (expression.bv_nat 1 0) v_20);
      let v_22 <- eval (add v_19 v_21);
      let (v_23 : expression (bv 16)) <- eval (extract v_22 1 17);
      let (v_24 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_25 <- eval (concat (expression.bv_nat 1 0) v_24);
      let (v_26 : expression (bv 16)) <- eval (extract v_7 48 64);
      let v_27 <- eval (concat (expression.bv_nat 1 0) v_26);
      let v_28 <- eval (add v_25 v_27);
      let (v_29 : expression (bv 16)) <- eval (extract v_28 1 17);
      let (v_30 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_31 <- eval (concat (expression.bv_nat 1 0) v_30);
      let (v_32 : expression (bv 16)) <- eval (extract v_7 64 80);
      let v_33 <- eval (concat (expression.bv_nat 1 0) v_32);
      let v_34 <- eval (add v_31 v_33);
      let (v_35 : expression (bv 16)) <- eval (extract v_34 1 17);
      let (v_36 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_37 <- eval (concat (expression.bv_nat 1 0) v_36);
      let (v_38 : expression (bv 16)) <- eval (extract v_7 80 96);
      let v_39 <- eval (concat (expression.bv_nat 1 0) v_38);
      let v_40 <- eval (add v_37 v_39);
      let (v_41 : expression (bv 16)) <- eval (extract v_40 1 17);
      let (v_42 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_43 <- eval (concat (expression.bv_nat 1 0) v_42);
      let (v_44 : expression (bv 16)) <- eval (extract v_7 96 112);
      let v_45 <- eval (concat (expression.bv_nat 1 0) v_44);
      let v_46 <- eval (add v_43 v_45);
      let (v_47 : expression (bv 16)) <- eval (extract v_46 1 17);
      let (v_48 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_49 <- eval (concat (expression.bv_nat 1 0) v_48);
      let (v_50 : expression (bv 16)) <- eval (extract v_7 112 128);
      let v_51 <- eval (concat (expression.bv_nat 1 0) v_50);
      let v_52 <- eval (add v_49 v_51);
      let (v_53 : expression (bv 16)) <- eval (extract v_52 1 17);
      let v_54 <- eval (concat (mux (isBitSet v_46 0) (expression.bv_nat 16 65535) v_47) (mux (isBitSet v_52 0) (expression.bv_nat 16 65535) v_53));
      let v_55 <- eval (concat (mux (isBitSet v_40 0) (expression.bv_nat 16 65535) v_41) v_54);
      let v_56 <- eval (concat (mux (isBitSet v_34 0) (expression.bv_nat 16 65535) v_35) v_55);
      let v_57 <- eval (concat (mux (isBitSet v_28 0) (expression.bv_nat 16 65535) v_29) v_56);
      let v_58 <- eval (concat (mux (isBitSet v_22 0) (expression.bv_nat 16 65535) v_23) v_57);
      let v_59 <- eval (concat (mux (isBitSet v_16 0) (expression.bv_nat 16 65535) v_17) v_58);
      let v_60 <- eval (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) v_11) v_59);
      setRegister (lhs.of_reg xmm_2) v_60;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 32;
      let (v_8 : expression (bv 16)) <- eval (extract v_7 0 16);
      let v_9 <- eval (concat (expression.bv_nat 1 0) v_8);
      let v_10 <- eval (add v_5 v_9);
      let (v_11 : expression (bv 16)) <- eval (extract v_10 1 17);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_13 <- eval (concat (expression.bv_nat 1 0) v_12);
      let (v_14 : expression (bv 16)) <- eval (extract v_7 16 32);
      let v_15 <- eval (concat (expression.bv_nat 1 0) v_14);
      let v_16 <- eval (add v_13 v_15);
      let (v_17 : expression (bv 16)) <- eval (extract v_16 1 17);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_19 <- eval (concat (expression.bv_nat 1 0) v_18);
      let (v_20 : expression (bv 16)) <- eval (extract v_7 32 48);
      let v_21 <- eval (concat (expression.bv_nat 1 0) v_20);
      let v_22 <- eval (add v_19 v_21);
      let (v_23 : expression (bv 16)) <- eval (extract v_22 1 17);
      let (v_24 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_25 <- eval (concat (expression.bv_nat 1 0) v_24);
      let (v_26 : expression (bv 16)) <- eval (extract v_7 48 64);
      let v_27 <- eval (concat (expression.bv_nat 1 0) v_26);
      let v_28 <- eval (add v_25 v_27);
      let (v_29 : expression (bv 16)) <- eval (extract v_28 1 17);
      let (v_30 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_31 <- eval (concat (expression.bv_nat 1 0) v_30);
      let (v_32 : expression (bv 16)) <- eval (extract v_7 64 80);
      let v_33 <- eval (concat (expression.bv_nat 1 0) v_32);
      let v_34 <- eval (add v_31 v_33);
      let (v_35 : expression (bv 16)) <- eval (extract v_34 1 17);
      let (v_36 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_37 <- eval (concat (expression.bv_nat 1 0) v_36);
      let (v_38 : expression (bv 16)) <- eval (extract v_7 80 96);
      let v_39 <- eval (concat (expression.bv_nat 1 0) v_38);
      let v_40 <- eval (add v_37 v_39);
      let (v_41 : expression (bv 16)) <- eval (extract v_40 1 17);
      let (v_42 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_43 <- eval (concat (expression.bv_nat 1 0) v_42);
      let (v_44 : expression (bv 16)) <- eval (extract v_7 96 112);
      let v_45 <- eval (concat (expression.bv_nat 1 0) v_44);
      let v_46 <- eval (add v_43 v_45);
      let (v_47 : expression (bv 16)) <- eval (extract v_46 1 17);
      let (v_48 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_49 <- eval (concat (expression.bv_nat 1 0) v_48);
      let (v_50 : expression (bv 16)) <- eval (extract v_7 112 128);
      let v_51 <- eval (concat (expression.bv_nat 1 0) v_50);
      let v_52 <- eval (add v_49 v_51);
      let (v_53 : expression (bv 16)) <- eval (extract v_52 1 17);
      let (v_54 : expression (bv 16)) <- eval (extract v_3 128 144);
      let v_55 <- eval (concat (expression.bv_nat 1 0) v_54);
      let (v_56 : expression (bv 16)) <- eval (extract v_7 128 144);
      let v_57 <- eval (concat (expression.bv_nat 1 0) v_56);
      let v_58 <- eval (add v_55 v_57);
      let (v_59 : expression (bv 16)) <- eval (extract v_58 1 17);
      let (v_60 : expression (bv 16)) <- eval (extract v_3 144 160);
      let v_61 <- eval (concat (expression.bv_nat 1 0) v_60);
      let (v_62 : expression (bv 16)) <- eval (extract v_7 144 160);
      let v_63 <- eval (concat (expression.bv_nat 1 0) v_62);
      let v_64 <- eval (add v_61 v_63);
      let (v_65 : expression (bv 16)) <- eval (extract v_64 1 17);
      let (v_66 : expression (bv 16)) <- eval (extract v_3 160 176);
      let v_67 <- eval (concat (expression.bv_nat 1 0) v_66);
      let (v_68 : expression (bv 16)) <- eval (extract v_7 160 176);
      let v_69 <- eval (concat (expression.bv_nat 1 0) v_68);
      let v_70 <- eval (add v_67 v_69);
      let (v_71 : expression (bv 16)) <- eval (extract v_70 1 17);
      let (v_72 : expression (bv 16)) <- eval (extract v_3 176 192);
      let v_73 <- eval (concat (expression.bv_nat 1 0) v_72);
      let (v_74 : expression (bv 16)) <- eval (extract v_7 176 192);
      let v_75 <- eval (concat (expression.bv_nat 1 0) v_74);
      let v_76 <- eval (add v_73 v_75);
      let (v_77 : expression (bv 16)) <- eval (extract v_76 1 17);
      let (v_78 : expression (bv 16)) <- eval (extract v_3 192 208);
      let v_79 <- eval (concat (expression.bv_nat 1 0) v_78);
      let (v_80 : expression (bv 16)) <- eval (extract v_7 192 208);
      let v_81 <- eval (concat (expression.bv_nat 1 0) v_80);
      let v_82 <- eval (add v_79 v_81);
      let (v_83 : expression (bv 16)) <- eval (extract v_82 1 17);
      let (v_84 : expression (bv 16)) <- eval (extract v_3 208 224);
      let v_85 <- eval (concat (expression.bv_nat 1 0) v_84);
      let (v_86 : expression (bv 16)) <- eval (extract v_7 208 224);
      let v_87 <- eval (concat (expression.bv_nat 1 0) v_86);
      let v_88 <- eval (add v_85 v_87);
      let (v_89 : expression (bv 16)) <- eval (extract v_88 1 17);
      let (v_90 : expression (bv 16)) <- eval (extract v_3 224 240);
      let v_91 <- eval (concat (expression.bv_nat 1 0) v_90);
      let (v_92 : expression (bv 16)) <- eval (extract v_7 224 240);
      let v_93 <- eval (concat (expression.bv_nat 1 0) v_92);
      let v_94 <- eval (add v_91 v_93);
      let (v_95 : expression (bv 16)) <- eval (extract v_94 1 17);
      let (v_96 : expression (bv 16)) <- eval (extract v_3 240 256);
      let v_97 <- eval (concat (expression.bv_nat 1 0) v_96);
      let (v_98 : expression (bv 16)) <- eval (extract v_7 240 256);
      let v_99 <- eval (concat (expression.bv_nat 1 0) v_98);
      let v_100 <- eval (add v_97 v_99);
      let (v_101 : expression (bv 16)) <- eval (extract v_100 1 17);
      let v_102 <- eval (concat (mux (isBitSet v_94 0) (expression.bv_nat 16 65535) v_95) (mux (isBitSet v_100 0) (expression.bv_nat 16 65535) v_101));
      let v_103 <- eval (concat (mux (isBitSet v_88 0) (expression.bv_nat 16 65535) v_89) v_102);
      let v_104 <- eval (concat (mux (isBitSet v_82 0) (expression.bv_nat 16 65535) v_83) v_103);
      let v_105 <- eval (concat (mux (isBitSet v_76 0) (expression.bv_nat 16 65535) v_77) v_104);
      let v_106 <- eval (concat (mux (isBitSet v_70 0) (expression.bv_nat 16 65535) v_71) v_105);
      let v_107 <- eval (concat (mux (isBitSet v_64 0) (expression.bv_nat 16 65535) v_65) v_106);
      let v_108 <- eval (concat (mux (isBitSet v_58 0) (expression.bv_nat 16 65535) v_59) v_107);
      let v_109 <- eval (concat (mux (isBitSet v_52 0) (expression.bv_nat 16 65535) v_53) v_108);
      let v_110 <- eval (concat (mux (isBitSet v_46 0) (expression.bv_nat 16 65535) v_47) v_109);
      let v_111 <- eval (concat (mux (isBitSet v_40 0) (expression.bv_nat 16 65535) v_41) v_110);
      let v_112 <- eval (concat (mux (isBitSet v_34 0) (expression.bv_nat 16 65535) v_35) v_111);
      let v_113 <- eval (concat (mux (isBitSet v_28 0) (expression.bv_nat 16 65535) v_29) v_112);
      let v_114 <- eval (concat (mux (isBitSet v_22 0) (expression.bv_nat 16 65535) v_23) v_113);
      let v_115 <- eval (concat (mux (isBitSet v_16 0) (expression.bv_nat 16 65535) v_17) v_114);
      let v_116 <- eval (concat (mux (isBitSet v_10 0) (expression.bv_nat 16 65535) v_11) v_115);
      setRegister (lhs.of_reg ymm_2) v_116;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- getRegister (lhs.of_reg xmm_0);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let v_8 <- eval (concat (expression.bv_nat 1 0) v_7);
      let v_9 <- eval (add v_5 v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_9 1 17);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_12 <- eval (concat (expression.bv_nat 1 0) v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 16 32);
      let v_14 <- eval (concat (expression.bv_nat 1 0) v_13);
      let v_15 <- eval (add v_12 v_14);
      let (v_16 : expression (bv 16)) <- eval (extract v_15 1 17);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_18 <- eval (concat (expression.bv_nat 1 0) v_17);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 32 48);
      let v_20 <- eval (concat (expression.bv_nat 1 0) v_19);
      let v_21 <- eval (add v_18 v_20);
      let (v_22 : expression (bv 16)) <- eval (extract v_21 1 17);
      let (v_23 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_24 <- eval (concat (expression.bv_nat 1 0) v_23);
      let (v_25 : expression (bv 16)) <- eval (extract v_6 48 64);
      let v_26 <- eval (concat (expression.bv_nat 1 0) v_25);
      let v_27 <- eval (add v_24 v_26);
      let (v_28 : expression (bv 16)) <- eval (extract v_27 1 17);
      let (v_29 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_30 <- eval (concat (expression.bv_nat 1 0) v_29);
      let (v_31 : expression (bv 16)) <- eval (extract v_6 64 80);
      let v_32 <- eval (concat (expression.bv_nat 1 0) v_31);
      let v_33 <- eval (add v_30 v_32);
      let (v_34 : expression (bv 16)) <- eval (extract v_33 1 17);
      let (v_35 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_36 <- eval (concat (expression.bv_nat 1 0) v_35);
      let (v_37 : expression (bv 16)) <- eval (extract v_6 80 96);
      let v_38 <- eval (concat (expression.bv_nat 1 0) v_37);
      let v_39 <- eval (add v_36 v_38);
      let (v_40 : expression (bv 16)) <- eval (extract v_39 1 17);
      let (v_41 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_42 <- eval (concat (expression.bv_nat 1 0) v_41);
      let (v_43 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_44 <- eval (concat (expression.bv_nat 1 0) v_43);
      let v_45 <- eval (add v_42 v_44);
      let (v_46 : expression (bv 16)) <- eval (extract v_45 1 17);
      let (v_47 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_48 <- eval (concat (expression.bv_nat 1 0) v_47);
      let (v_49 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_50 <- eval (concat (expression.bv_nat 1 0) v_49);
      let v_51 <- eval (add v_48 v_50);
      let (v_52 : expression (bv 16)) <- eval (extract v_51 1 17);
      let v_53 <- eval (concat (mux (isBitSet v_45 0) (expression.bv_nat 16 65535) v_46) (mux (isBitSet v_51 0) (expression.bv_nat 16 65535) v_52));
      let v_54 <- eval (concat (mux (isBitSet v_39 0) (expression.bv_nat 16 65535) v_40) v_53);
      let v_55 <- eval (concat (mux (isBitSet v_33 0) (expression.bv_nat 16 65535) v_34) v_54);
      let v_56 <- eval (concat (mux (isBitSet v_27 0) (expression.bv_nat 16 65535) v_28) v_55);
      let v_57 <- eval (concat (mux (isBitSet v_21 0) (expression.bv_nat 16 65535) v_22) v_56);
      let v_58 <- eval (concat (mux (isBitSet v_15 0) (expression.bv_nat 16 65535) v_16) v_57);
      let v_59 <- eval (concat (mux (isBitSet v_9 0) (expression.bv_nat 16 65535) v_10) v_58);
      setRegister (lhs.of_reg xmm_2) v_59;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let v_6 <- getRegister (lhs.of_reg ymm_0);
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let v_8 <- eval (concat (expression.bv_nat 1 0) v_7);
      let v_9 <- eval (add v_5 v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_9 1 17);
      let (v_11 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_12 <- eval (concat (expression.bv_nat 1 0) v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_6 16 32);
      let v_14 <- eval (concat (expression.bv_nat 1 0) v_13);
      let v_15 <- eval (add v_12 v_14);
      let (v_16 : expression (bv 16)) <- eval (extract v_15 1 17);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_18 <- eval (concat (expression.bv_nat 1 0) v_17);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 32 48);
      let v_20 <- eval (concat (expression.bv_nat 1 0) v_19);
      let v_21 <- eval (add v_18 v_20);
      let (v_22 : expression (bv 16)) <- eval (extract v_21 1 17);
      let (v_23 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_24 <- eval (concat (expression.bv_nat 1 0) v_23);
      let (v_25 : expression (bv 16)) <- eval (extract v_6 48 64);
      let v_26 <- eval (concat (expression.bv_nat 1 0) v_25);
      let v_27 <- eval (add v_24 v_26);
      let (v_28 : expression (bv 16)) <- eval (extract v_27 1 17);
      let (v_29 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_30 <- eval (concat (expression.bv_nat 1 0) v_29);
      let (v_31 : expression (bv 16)) <- eval (extract v_6 64 80);
      let v_32 <- eval (concat (expression.bv_nat 1 0) v_31);
      let v_33 <- eval (add v_30 v_32);
      let (v_34 : expression (bv 16)) <- eval (extract v_33 1 17);
      let (v_35 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_36 <- eval (concat (expression.bv_nat 1 0) v_35);
      let (v_37 : expression (bv 16)) <- eval (extract v_6 80 96);
      let v_38 <- eval (concat (expression.bv_nat 1 0) v_37);
      let v_39 <- eval (add v_36 v_38);
      let (v_40 : expression (bv 16)) <- eval (extract v_39 1 17);
      let (v_41 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_42 <- eval (concat (expression.bv_nat 1 0) v_41);
      let (v_43 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_44 <- eval (concat (expression.bv_nat 1 0) v_43);
      let v_45 <- eval (add v_42 v_44);
      let (v_46 : expression (bv 16)) <- eval (extract v_45 1 17);
      let (v_47 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_48 <- eval (concat (expression.bv_nat 1 0) v_47);
      let (v_49 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_50 <- eval (concat (expression.bv_nat 1 0) v_49);
      let v_51 <- eval (add v_48 v_50);
      let (v_52 : expression (bv 16)) <- eval (extract v_51 1 17);
      let (v_53 : expression (bv 16)) <- eval (extract v_3 128 144);
      let v_54 <- eval (concat (expression.bv_nat 1 0) v_53);
      let (v_55 : expression (bv 16)) <- eval (extract v_6 128 144);
      let v_56 <- eval (concat (expression.bv_nat 1 0) v_55);
      let v_57 <- eval (add v_54 v_56);
      let (v_58 : expression (bv 16)) <- eval (extract v_57 1 17);
      let (v_59 : expression (bv 16)) <- eval (extract v_3 144 160);
      let v_60 <- eval (concat (expression.bv_nat 1 0) v_59);
      let (v_61 : expression (bv 16)) <- eval (extract v_6 144 160);
      let v_62 <- eval (concat (expression.bv_nat 1 0) v_61);
      let v_63 <- eval (add v_60 v_62);
      let (v_64 : expression (bv 16)) <- eval (extract v_63 1 17);
      let (v_65 : expression (bv 16)) <- eval (extract v_3 160 176);
      let v_66 <- eval (concat (expression.bv_nat 1 0) v_65);
      let (v_67 : expression (bv 16)) <- eval (extract v_6 160 176);
      let v_68 <- eval (concat (expression.bv_nat 1 0) v_67);
      let v_69 <- eval (add v_66 v_68);
      let (v_70 : expression (bv 16)) <- eval (extract v_69 1 17);
      let (v_71 : expression (bv 16)) <- eval (extract v_3 176 192);
      let v_72 <- eval (concat (expression.bv_nat 1 0) v_71);
      let (v_73 : expression (bv 16)) <- eval (extract v_6 176 192);
      let v_74 <- eval (concat (expression.bv_nat 1 0) v_73);
      let v_75 <- eval (add v_72 v_74);
      let (v_76 : expression (bv 16)) <- eval (extract v_75 1 17);
      let (v_77 : expression (bv 16)) <- eval (extract v_3 192 208);
      let v_78 <- eval (concat (expression.bv_nat 1 0) v_77);
      let (v_79 : expression (bv 16)) <- eval (extract v_6 192 208);
      let v_80 <- eval (concat (expression.bv_nat 1 0) v_79);
      let v_81 <- eval (add v_78 v_80);
      let (v_82 : expression (bv 16)) <- eval (extract v_81 1 17);
      let (v_83 : expression (bv 16)) <- eval (extract v_3 208 224);
      let v_84 <- eval (concat (expression.bv_nat 1 0) v_83);
      let (v_85 : expression (bv 16)) <- eval (extract v_6 208 224);
      let v_86 <- eval (concat (expression.bv_nat 1 0) v_85);
      let v_87 <- eval (add v_84 v_86);
      let (v_88 : expression (bv 16)) <- eval (extract v_87 1 17);
      let (v_89 : expression (bv 16)) <- eval (extract v_3 224 240);
      let v_90 <- eval (concat (expression.bv_nat 1 0) v_89);
      let (v_91 : expression (bv 16)) <- eval (extract v_6 224 240);
      let v_92 <- eval (concat (expression.bv_nat 1 0) v_91);
      let v_93 <- eval (add v_90 v_92);
      let (v_94 : expression (bv 16)) <- eval (extract v_93 1 17);
      let (v_95 : expression (bv 16)) <- eval (extract v_3 240 256);
      let v_96 <- eval (concat (expression.bv_nat 1 0) v_95);
      let (v_97 : expression (bv 16)) <- eval (extract v_6 240 256);
      let v_98 <- eval (concat (expression.bv_nat 1 0) v_97);
      let v_99 <- eval (add v_96 v_98);
      let (v_100 : expression (bv 16)) <- eval (extract v_99 1 17);
      let v_101 <- eval (concat (mux (isBitSet v_93 0) (expression.bv_nat 16 65535) v_94) (mux (isBitSet v_99 0) (expression.bv_nat 16 65535) v_100));
      let v_102 <- eval (concat (mux (isBitSet v_87 0) (expression.bv_nat 16 65535) v_88) v_101);
      let v_103 <- eval (concat (mux (isBitSet v_81 0) (expression.bv_nat 16 65535) v_82) v_102);
      let v_104 <- eval (concat (mux (isBitSet v_75 0) (expression.bv_nat 16 65535) v_76) v_103);
      let v_105 <- eval (concat (mux (isBitSet v_69 0) (expression.bv_nat 16 65535) v_70) v_104);
      let v_106 <- eval (concat (mux (isBitSet v_63 0) (expression.bv_nat 16 65535) v_64) v_105);
      let v_107 <- eval (concat (mux (isBitSet v_57 0) (expression.bv_nat 16 65535) v_58) v_106);
      let v_108 <- eval (concat (mux (isBitSet v_51 0) (expression.bv_nat 16 65535) v_52) v_107);
      let v_109 <- eval (concat (mux (isBitSet v_45 0) (expression.bv_nat 16 65535) v_46) v_108);
      let v_110 <- eval (concat (mux (isBitSet v_39 0) (expression.bv_nat 16 65535) v_40) v_109);
      let v_111 <- eval (concat (mux (isBitSet v_33 0) (expression.bv_nat 16 65535) v_34) v_110);
      let v_112 <- eval (concat (mux (isBitSet v_27 0) (expression.bv_nat 16 65535) v_28) v_111);
      let v_113 <- eval (concat (mux (isBitSet v_21 0) (expression.bv_nat 16 65535) v_22) v_112);
      let v_114 <- eval (concat (mux (isBitSet v_15 0) (expression.bv_nat 16 65535) v_16) v_113);
      let v_115 <- eval (concat (mux (isBitSet v_9 0) (expression.bv_nat 16 65535) v_10) v_114);
      setRegister (lhs.of_reg ymm_2) v_115;
      pure ()
     action

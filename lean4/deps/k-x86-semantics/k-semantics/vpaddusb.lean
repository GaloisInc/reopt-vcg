def vpaddusb : instruction :=
  definst "vpaddusb" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      (v_7 : expression (bv 8)) <- eval (extract v_6 0 8);
      v_8 <- eval (add (concat (expression.bv_nat 1 0) v_4) (concat (expression.bv_nat 1 0) v_7));
      (v_9 : expression (bv 8)) <- eval (extract v_8 1 9);
      (v_10 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_11 : expression (bv 8)) <- eval (extract v_6 8 16);
      v_12 <- eval (add (concat (expression.bv_nat 1 0) v_10) (concat (expression.bv_nat 1 0) v_11));
      (v_13 : expression (bv 8)) <- eval (extract v_12 1 9);
      (v_14 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_15 : expression (bv 8)) <- eval (extract v_6 16 24);
      v_16 <- eval (add (concat (expression.bv_nat 1 0) v_14) (concat (expression.bv_nat 1 0) v_15));
      (v_17 : expression (bv 8)) <- eval (extract v_16 1 9);
      (v_18 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_19 : expression (bv 8)) <- eval (extract v_6 24 32);
      v_20 <- eval (add (concat (expression.bv_nat 1 0) v_18) (concat (expression.bv_nat 1 0) v_19));
      (v_21 : expression (bv 8)) <- eval (extract v_20 1 9);
      (v_22 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_23 : expression (bv 8)) <- eval (extract v_6 32 40);
      v_24 <- eval (add (concat (expression.bv_nat 1 0) v_22) (concat (expression.bv_nat 1 0) v_23));
      (v_25 : expression (bv 8)) <- eval (extract v_24 1 9);
      (v_26 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_27 : expression (bv 8)) <- eval (extract v_6 40 48);
      v_28 <- eval (add (concat (expression.bv_nat 1 0) v_26) (concat (expression.bv_nat 1 0) v_27));
      (v_29 : expression (bv 8)) <- eval (extract v_28 1 9);
      (v_30 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_31 : expression (bv 8)) <- eval (extract v_6 48 56);
      v_32 <- eval (add (concat (expression.bv_nat 1 0) v_30) (concat (expression.bv_nat 1 0) v_31));
      (v_33 : expression (bv 8)) <- eval (extract v_32 1 9);
      (v_34 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_35 : expression (bv 8)) <- eval (extract v_6 56 64);
      v_36 <- eval (add (concat (expression.bv_nat 1 0) v_34) (concat (expression.bv_nat 1 0) v_35));
      (v_37 : expression (bv 8)) <- eval (extract v_36 1 9);
      (v_38 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_39 : expression (bv 8)) <- eval (extract v_6 64 72);
      v_40 <- eval (add (concat (expression.bv_nat 1 0) v_38) (concat (expression.bv_nat 1 0) v_39));
      (v_41 : expression (bv 8)) <- eval (extract v_40 1 9);
      (v_42 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_43 : expression (bv 8)) <- eval (extract v_6 72 80);
      v_44 <- eval (add (concat (expression.bv_nat 1 0) v_42) (concat (expression.bv_nat 1 0) v_43));
      (v_45 : expression (bv 8)) <- eval (extract v_44 1 9);
      (v_46 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_47 : expression (bv 8)) <- eval (extract v_6 80 88);
      v_48 <- eval (add (concat (expression.bv_nat 1 0) v_46) (concat (expression.bv_nat 1 0) v_47));
      (v_49 : expression (bv 8)) <- eval (extract v_48 1 9);
      (v_50 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_51 : expression (bv 8)) <- eval (extract v_6 88 96);
      v_52 <- eval (add (concat (expression.bv_nat 1 0) v_50) (concat (expression.bv_nat 1 0) v_51));
      (v_53 : expression (bv 8)) <- eval (extract v_52 1 9);
      (v_54 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_55 : expression (bv 8)) <- eval (extract v_6 96 104);
      v_56 <- eval (add (concat (expression.bv_nat 1 0) v_54) (concat (expression.bv_nat 1 0) v_55));
      (v_57 : expression (bv 8)) <- eval (extract v_56 1 9);
      (v_58 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_59 : expression (bv 8)) <- eval (extract v_6 104 112);
      v_60 <- eval (add (concat (expression.bv_nat 1 0) v_58) (concat (expression.bv_nat 1 0) v_59));
      (v_61 : expression (bv 8)) <- eval (extract v_60 1 9);
      (v_62 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_63 : expression (bv 8)) <- eval (extract v_6 112 120);
      v_64 <- eval (add (concat (expression.bv_nat 1 0) v_62) (concat (expression.bv_nat 1 0) v_63));
      (v_65 : expression (bv 8)) <- eval (extract v_64 1 9);
      (v_66 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_67 : expression (bv 8)) <- eval (extract v_6 120 128);
      v_68 <- eval (add (concat (expression.bv_nat 1 0) v_66) (concat (expression.bv_nat 1 0) v_67));
      (v_69 : expression (bv 8)) <- eval (extract v_68 1 9);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_8 0) (expression.bv_nat 8 255) v_9) (concat (mux (isBitSet v_12 0) (expression.bv_nat 8 255) v_13) (concat (mux (isBitSet v_16 0) (expression.bv_nat 8 255) v_17) (concat (mux (isBitSet v_20 0) (expression.bv_nat 8 255) v_21) (concat (mux (isBitSet v_24 0) (expression.bv_nat 8 255) v_25) (concat (mux (isBitSet v_28 0) (expression.bv_nat 8 255) v_29) (concat (mux (isBitSet v_32 0) (expression.bv_nat 8 255) v_33) (concat (mux (isBitSet v_36 0) (expression.bv_nat 8 255) v_37) (concat (mux (isBitSet v_40 0) (expression.bv_nat 8 255) v_41) (concat (mux (isBitSet v_44 0) (expression.bv_nat 8 255) v_45) (concat (mux (isBitSet v_48 0) (expression.bv_nat 8 255) v_49) (concat (mux (isBitSet v_52 0) (expression.bv_nat 8 255) v_53) (concat (mux (isBitSet v_56 0) (expression.bv_nat 8 255) v_57) (concat (mux (isBitSet v_60 0) (expression.bv_nat 8 255) v_61) (concat (mux (isBitSet v_64 0) (expression.bv_nat 8 255) v_65) (mux (isBitSet v_68 0) (expression.bv_nat 8 255) v_69))))))))))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      (v_7 : expression (bv 8)) <- eval (extract v_6 0 8);
      v_8 <- eval (add (concat (expression.bv_nat 1 0) v_4) (concat (expression.bv_nat 1 0) v_7));
      (v_9 : expression (bv 8)) <- eval (extract v_8 1 9);
      (v_10 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_11 : expression (bv 8)) <- eval (extract v_6 8 16);
      v_12 <- eval (add (concat (expression.bv_nat 1 0) v_10) (concat (expression.bv_nat 1 0) v_11));
      (v_13 : expression (bv 8)) <- eval (extract v_12 1 9);
      (v_14 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_15 : expression (bv 8)) <- eval (extract v_6 16 24);
      v_16 <- eval (add (concat (expression.bv_nat 1 0) v_14) (concat (expression.bv_nat 1 0) v_15));
      (v_17 : expression (bv 8)) <- eval (extract v_16 1 9);
      (v_18 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_19 : expression (bv 8)) <- eval (extract v_6 24 32);
      v_20 <- eval (add (concat (expression.bv_nat 1 0) v_18) (concat (expression.bv_nat 1 0) v_19));
      (v_21 : expression (bv 8)) <- eval (extract v_20 1 9);
      (v_22 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_23 : expression (bv 8)) <- eval (extract v_6 32 40);
      v_24 <- eval (add (concat (expression.bv_nat 1 0) v_22) (concat (expression.bv_nat 1 0) v_23));
      (v_25 : expression (bv 8)) <- eval (extract v_24 1 9);
      (v_26 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_27 : expression (bv 8)) <- eval (extract v_6 40 48);
      v_28 <- eval (add (concat (expression.bv_nat 1 0) v_26) (concat (expression.bv_nat 1 0) v_27));
      (v_29 : expression (bv 8)) <- eval (extract v_28 1 9);
      (v_30 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_31 : expression (bv 8)) <- eval (extract v_6 48 56);
      v_32 <- eval (add (concat (expression.bv_nat 1 0) v_30) (concat (expression.bv_nat 1 0) v_31));
      (v_33 : expression (bv 8)) <- eval (extract v_32 1 9);
      (v_34 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_35 : expression (bv 8)) <- eval (extract v_6 56 64);
      v_36 <- eval (add (concat (expression.bv_nat 1 0) v_34) (concat (expression.bv_nat 1 0) v_35));
      (v_37 : expression (bv 8)) <- eval (extract v_36 1 9);
      (v_38 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_39 : expression (bv 8)) <- eval (extract v_6 64 72);
      v_40 <- eval (add (concat (expression.bv_nat 1 0) v_38) (concat (expression.bv_nat 1 0) v_39));
      (v_41 : expression (bv 8)) <- eval (extract v_40 1 9);
      (v_42 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_43 : expression (bv 8)) <- eval (extract v_6 72 80);
      v_44 <- eval (add (concat (expression.bv_nat 1 0) v_42) (concat (expression.bv_nat 1 0) v_43));
      (v_45 : expression (bv 8)) <- eval (extract v_44 1 9);
      (v_46 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_47 : expression (bv 8)) <- eval (extract v_6 80 88);
      v_48 <- eval (add (concat (expression.bv_nat 1 0) v_46) (concat (expression.bv_nat 1 0) v_47));
      (v_49 : expression (bv 8)) <- eval (extract v_48 1 9);
      (v_50 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_51 : expression (bv 8)) <- eval (extract v_6 88 96);
      v_52 <- eval (add (concat (expression.bv_nat 1 0) v_50) (concat (expression.bv_nat 1 0) v_51));
      (v_53 : expression (bv 8)) <- eval (extract v_52 1 9);
      (v_54 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_55 : expression (bv 8)) <- eval (extract v_6 96 104);
      v_56 <- eval (add (concat (expression.bv_nat 1 0) v_54) (concat (expression.bv_nat 1 0) v_55));
      (v_57 : expression (bv 8)) <- eval (extract v_56 1 9);
      (v_58 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_59 : expression (bv 8)) <- eval (extract v_6 104 112);
      v_60 <- eval (add (concat (expression.bv_nat 1 0) v_58) (concat (expression.bv_nat 1 0) v_59));
      (v_61 : expression (bv 8)) <- eval (extract v_60 1 9);
      (v_62 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_63 : expression (bv 8)) <- eval (extract v_6 112 120);
      v_64 <- eval (add (concat (expression.bv_nat 1 0) v_62) (concat (expression.bv_nat 1 0) v_63));
      (v_65 : expression (bv 8)) <- eval (extract v_64 1 9);
      (v_66 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_67 : expression (bv 8)) <- eval (extract v_6 120 128);
      v_68 <- eval (add (concat (expression.bv_nat 1 0) v_66) (concat (expression.bv_nat 1 0) v_67));
      (v_69 : expression (bv 8)) <- eval (extract v_68 1 9);
      (v_70 : expression (bv 8)) <- eval (extract v_3 128 136);
      (v_71 : expression (bv 8)) <- eval (extract v_6 128 136);
      v_72 <- eval (add (concat (expression.bv_nat 1 0) v_70) (concat (expression.bv_nat 1 0) v_71));
      (v_73 : expression (bv 8)) <- eval (extract v_72 1 9);
      (v_74 : expression (bv 8)) <- eval (extract v_3 136 144);
      (v_75 : expression (bv 8)) <- eval (extract v_6 136 144);
      v_76 <- eval (add (concat (expression.bv_nat 1 0) v_74) (concat (expression.bv_nat 1 0) v_75));
      (v_77 : expression (bv 8)) <- eval (extract v_76 1 9);
      (v_78 : expression (bv 8)) <- eval (extract v_3 144 152);
      (v_79 : expression (bv 8)) <- eval (extract v_6 144 152);
      v_80 <- eval (add (concat (expression.bv_nat 1 0) v_78) (concat (expression.bv_nat 1 0) v_79));
      (v_81 : expression (bv 8)) <- eval (extract v_80 1 9);
      (v_82 : expression (bv 8)) <- eval (extract v_3 152 160);
      (v_83 : expression (bv 8)) <- eval (extract v_6 152 160);
      v_84 <- eval (add (concat (expression.bv_nat 1 0) v_82) (concat (expression.bv_nat 1 0) v_83));
      (v_85 : expression (bv 8)) <- eval (extract v_84 1 9);
      (v_86 : expression (bv 8)) <- eval (extract v_3 160 168);
      (v_87 : expression (bv 8)) <- eval (extract v_6 160 168);
      v_88 <- eval (add (concat (expression.bv_nat 1 0) v_86) (concat (expression.bv_nat 1 0) v_87));
      (v_89 : expression (bv 8)) <- eval (extract v_88 1 9);
      (v_90 : expression (bv 8)) <- eval (extract v_3 168 176);
      (v_91 : expression (bv 8)) <- eval (extract v_6 168 176);
      v_92 <- eval (add (concat (expression.bv_nat 1 0) v_90) (concat (expression.bv_nat 1 0) v_91));
      (v_93 : expression (bv 8)) <- eval (extract v_92 1 9);
      (v_94 : expression (bv 8)) <- eval (extract v_3 176 184);
      (v_95 : expression (bv 8)) <- eval (extract v_6 176 184);
      v_96 <- eval (add (concat (expression.bv_nat 1 0) v_94) (concat (expression.bv_nat 1 0) v_95));
      (v_97 : expression (bv 8)) <- eval (extract v_96 1 9);
      (v_98 : expression (bv 8)) <- eval (extract v_3 184 192);
      (v_99 : expression (bv 8)) <- eval (extract v_6 184 192);
      v_100 <- eval (add (concat (expression.bv_nat 1 0) v_98) (concat (expression.bv_nat 1 0) v_99));
      (v_101 : expression (bv 8)) <- eval (extract v_100 1 9);
      (v_102 : expression (bv 8)) <- eval (extract v_3 192 200);
      (v_103 : expression (bv 8)) <- eval (extract v_6 192 200);
      v_104 <- eval (add (concat (expression.bv_nat 1 0) v_102) (concat (expression.bv_nat 1 0) v_103));
      (v_105 : expression (bv 8)) <- eval (extract v_104 1 9);
      (v_106 : expression (bv 8)) <- eval (extract v_3 200 208);
      (v_107 : expression (bv 8)) <- eval (extract v_6 200 208);
      v_108 <- eval (add (concat (expression.bv_nat 1 0) v_106) (concat (expression.bv_nat 1 0) v_107));
      (v_109 : expression (bv 8)) <- eval (extract v_108 1 9);
      (v_110 : expression (bv 8)) <- eval (extract v_3 208 216);
      (v_111 : expression (bv 8)) <- eval (extract v_6 208 216);
      v_112 <- eval (add (concat (expression.bv_nat 1 0) v_110) (concat (expression.bv_nat 1 0) v_111));
      (v_113 : expression (bv 8)) <- eval (extract v_112 1 9);
      (v_114 : expression (bv 8)) <- eval (extract v_3 216 224);
      (v_115 : expression (bv 8)) <- eval (extract v_6 216 224);
      v_116 <- eval (add (concat (expression.bv_nat 1 0) v_114) (concat (expression.bv_nat 1 0) v_115));
      (v_117 : expression (bv 8)) <- eval (extract v_116 1 9);
      (v_118 : expression (bv 8)) <- eval (extract v_3 224 232);
      (v_119 : expression (bv 8)) <- eval (extract v_6 224 232);
      v_120 <- eval (add (concat (expression.bv_nat 1 0) v_118) (concat (expression.bv_nat 1 0) v_119));
      (v_121 : expression (bv 8)) <- eval (extract v_120 1 9);
      (v_122 : expression (bv 8)) <- eval (extract v_3 232 240);
      (v_123 : expression (bv 8)) <- eval (extract v_6 232 240);
      v_124 <- eval (add (concat (expression.bv_nat 1 0) v_122) (concat (expression.bv_nat 1 0) v_123));
      (v_125 : expression (bv 8)) <- eval (extract v_124 1 9);
      (v_126 : expression (bv 8)) <- eval (extract v_3 240 248);
      (v_127 : expression (bv 8)) <- eval (extract v_6 240 248);
      v_128 <- eval (add (concat (expression.bv_nat 1 0) v_126) (concat (expression.bv_nat 1 0) v_127));
      (v_129 : expression (bv 8)) <- eval (extract v_128 1 9);
      (v_130 : expression (bv 8)) <- eval (extract v_3 248 256);
      (v_131 : expression (bv 8)) <- eval (extract v_6 248 256);
      v_132 <- eval (add (concat (expression.bv_nat 1 0) v_130) (concat (expression.bv_nat 1 0) v_131));
      (v_133 : expression (bv 8)) <- eval (extract v_132 1 9);
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitSet v_8 0) (expression.bv_nat 8 255) v_9) (concat (mux (isBitSet v_12 0) (expression.bv_nat 8 255) v_13) (concat (mux (isBitSet v_16 0) (expression.bv_nat 8 255) v_17) (concat (mux (isBitSet v_20 0) (expression.bv_nat 8 255) v_21) (concat (mux (isBitSet v_24 0) (expression.bv_nat 8 255) v_25) (concat (mux (isBitSet v_28 0) (expression.bv_nat 8 255) v_29) (concat (mux (isBitSet v_32 0) (expression.bv_nat 8 255) v_33) (concat (mux (isBitSet v_36 0) (expression.bv_nat 8 255) v_37) (concat (mux (isBitSet v_40 0) (expression.bv_nat 8 255) v_41) (concat (mux (isBitSet v_44 0) (expression.bv_nat 8 255) v_45) (concat (mux (isBitSet v_48 0) (expression.bv_nat 8 255) v_49) (concat (mux (isBitSet v_52 0) (expression.bv_nat 8 255) v_53) (concat (mux (isBitSet v_56 0) (expression.bv_nat 8 255) v_57) (concat (mux (isBitSet v_60 0) (expression.bv_nat 8 255) v_61) (concat (mux (isBitSet v_64 0) (expression.bv_nat 8 255) v_65) (concat (mux (isBitSet v_68 0) (expression.bv_nat 8 255) v_69) (concat (mux (isBitSet v_72 0) (expression.bv_nat 8 255) v_73) (concat (mux (isBitSet v_76 0) (expression.bv_nat 8 255) v_77) (concat (mux (isBitSet v_80 0) (expression.bv_nat 8 255) v_81) (concat (mux (isBitSet v_84 0) (expression.bv_nat 8 255) v_85) (concat (mux (isBitSet v_88 0) (expression.bv_nat 8 255) v_89) (concat (mux (isBitSet v_92 0) (expression.bv_nat 8 255) v_93) (concat (mux (isBitSet v_96 0) (expression.bv_nat 8 255) v_97) (concat (mux (isBitSet v_100 0) (expression.bv_nat 8 255) v_101) (concat (mux (isBitSet v_104 0) (expression.bv_nat 8 255) v_105) (concat (mux (isBitSet v_108 0) (expression.bv_nat 8 255) v_109) (concat (mux (isBitSet v_112 0) (expression.bv_nat 8 255) v_113) (concat (mux (isBitSet v_116 0) (expression.bv_nat 8 255) v_117) (concat (mux (isBitSet v_120 0) (expression.bv_nat 8 255) v_121) (concat (mux (isBitSet v_124 0) (expression.bv_nat 8 255) v_125) (concat (mux (isBitSet v_128 0) (expression.bv_nat 8 255) v_129) (mux (isBitSet v_132 0) (expression.bv_nat 8 255) v_133))))))))))))))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      v_7 <- eval (add (concat (expression.bv_nat 1 0) v_4) (concat (expression.bv_nat 1 0) v_6));
      (v_8 : expression (bv 8)) <- eval (extract v_7 1 9);
      (v_9 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_10 : expression (bv 8)) <- eval (extract v_5 8 16);
      v_11 <- eval (add (concat (expression.bv_nat 1 0) v_9) (concat (expression.bv_nat 1 0) v_10));
      (v_12 : expression (bv 8)) <- eval (extract v_11 1 9);
      (v_13 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_14 : expression (bv 8)) <- eval (extract v_5 16 24);
      v_15 <- eval (add (concat (expression.bv_nat 1 0) v_13) (concat (expression.bv_nat 1 0) v_14));
      (v_16 : expression (bv 8)) <- eval (extract v_15 1 9);
      (v_17 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_18 : expression (bv 8)) <- eval (extract v_5 24 32);
      v_19 <- eval (add (concat (expression.bv_nat 1 0) v_17) (concat (expression.bv_nat 1 0) v_18));
      (v_20 : expression (bv 8)) <- eval (extract v_19 1 9);
      (v_21 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_22 : expression (bv 8)) <- eval (extract v_5 32 40);
      v_23 <- eval (add (concat (expression.bv_nat 1 0) v_21) (concat (expression.bv_nat 1 0) v_22));
      (v_24 : expression (bv 8)) <- eval (extract v_23 1 9);
      (v_25 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_26 : expression (bv 8)) <- eval (extract v_5 40 48);
      v_27 <- eval (add (concat (expression.bv_nat 1 0) v_25) (concat (expression.bv_nat 1 0) v_26));
      (v_28 : expression (bv 8)) <- eval (extract v_27 1 9);
      (v_29 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_30 : expression (bv 8)) <- eval (extract v_5 48 56);
      v_31 <- eval (add (concat (expression.bv_nat 1 0) v_29) (concat (expression.bv_nat 1 0) v_30));
      (v_32 : expression (bv 8)) <- eval (extract v_31 1 9);
      (v_33 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_34 : expression (bv 8)) <- eval (extract v_5 56 64);
      v_35 <- eval (add (concat (expression.bv_nat 1 0) v_33) (concat (expression.bv_nat 1 0) v_34));
      (v_36 : expression (bv 8)) <- eval (extract v_35 1 9);
      (v_37 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_38 : expression (bv 8)) <- eval (extract v_5 64 72);
      v_39 <- eval (add (concat (expression.bv_nat 1 0) v_37) (concat (expression.bv_nat 1 0) v_38));
      (v_40 : expression (bv 8)) <- eval (extract v_39 1 9);
      (v_41 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_42 : expression (bv 8)) <- eval (extract v_5 72 80);
      v_43 <- eval (add (concat (expression.bv_nat 1 0) v_41) (concat (expression.bv_nat 1 0) v_42));
      (v_44 : expression (bv 8)) <- eval (extract v_43 1 9);
      (v_45 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_46 : expression (bv 8)) <- eval (extract v_5 80 88);
      v_47 <- eval (add (concat (expression.bv_nat 1 0) v_45) (concat (expression.bv_nat 1 0) v_46));
      (v_48 : expression (bv 8)) <- eval (extract v_47 1 9);
      (v_49 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_50 : expression (bv 8)) <- eval (extract v_5 88 96);
      v_51 <- eval (add (concat (expression.bv_nat 1 0) v_49) (concat (expression.bv_nat 1 0) v_50));
      (v_52 : expression (bv 8)) <- eval (extract v_51 1 9);
      (v_53 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_54 : expression (bv 8)) <- eval (extract v_5 96 104);
      v_55 <- eval (add (concat (expression.bv_nat 1 0) v_53) (concat (expression.bv_nat 1 0) v_54));
      (v_56 : expression (bv 8)) <- eval (extract v_55 1 9);
      (v_57 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_58 : expression (bv 8)) <- eval (extract v_5 104 112);
      v_59 <- eval (add (concat (expression.bv_nat 1 0) v_57) (concat (expression.bv_nat 1 0) v_58));
      (v_60 : expression (bv 8)) <- eval (extract v_59 1 9);
      (v_61 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_62 : expression (bv 8)) <- eval (extract v_5 112 120);
      v_63 <- eval (add (concat (expression.bv_nat 1 0) v_61) (concat (expression.bv_nat 1 0) v_62));
      (v_64 : expression (bv 8)) <- eval (extract v_63 1 9);
      (v_65 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_66 : expression (bv 8)) <- eval (extract v_5 120 128);
      v_67 <- eval (add (concat (expression.bv_nat 1 0) v_65) (concat (expression.bv_nat 1 0) v_66));
      (v_68 : expression (bv 8)) <- eval (extract v_67 1 9);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_7 0) (expression.bv_nat 8 255) v_8) (concat (mux (isBitSet v_11 0) (expression.bv_nat 8 255) v_12) (concat (mux (isBitSet v_15 0) (expression.bv_nat 8 255) v_16) (concat (mux (isBitSet v_19 0) (expression.bv_nat 8 255) v_20) (concat (mux (isBitSet v_23 0) (expression.bv_nat 8 255) v_24) (concat (mux (isBitSet v_27 0) (expression.bv_nat 8 255) v_28) (concat (mux (isBitSet v_31 0) (expression.bv_nat 8 255) v_32) (concat (mux (isBitSet v_35 0) (expression.bv_nat 8 255) v_36) (concat (mux (isBitSet v_39 0) (expression.bv_nat 8 255) v_40) (concat (mux (isBitSet v_43 0) (expression.bv_nat 8 255) v_44) (concat (mux (isBitSet v_47 0) (expression.bv_nat 8 255) v_48) (concat (mux (isBitSet v_51 0) (expression.bv_nat 8 255) v_52) (concat (mux (isBitSet v_55 0) (expression.bv_nat 8 255) v_56) (concat (mux (isBitSet v_59 0) (expression.bv_nat 8 255) v_60) (concat (mux (isBitSet v_63 0) (expression.bv_nat 8 255) v_64) (mux (isBitSet v_67 0) (expression.bv_nat 8 255) v_68))))))))))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      v_5 <- getRegister (lhs.of_reg ymm_0);
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      v_7 <- eval (add (concat (expression.bv_nat 1 0) v_4) (concat (expression.bv_nat 1 0) v_6));
      (v_8 : expression (bv 8)) <- eval (extract v_7 1 9);
      (v_9 : expression (bv 8)) <- eval (extract v_3 8 16);
      (v_10 : expression (bv 8)) <- eval (extract v_5 8 16);
      v_11 <- eval (add (concat (expression.bv_nat 1 0) v_9) (concat (expression.bv_nat 1 0) v_10));
      (v_12 : expression (bv 8)) <- eval (extract v_11 1 9);
      (v_13 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_14 : expression (bv 8)) <- eval (extract v_5 16 24);
      v_15 <- eval (add (concat (expression.bv_nat 1 0) v_13) (concat (expression.bv_nat 1 0) v_14));
      (v_16 : expression (bv 8)) <- eval (extract v_15 1 9);
      (v_17 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_18 : expression (bv 8)) <- eval (extract v_5 24 32);
      v_19 <- eval (add (concat (expression.bv_nat 1 0) v_17) (concat (expression.bv_nat 1 0) v_18));
      (v_20 : expression (bv 8)) <- eval (extract v_19 1 9);
      (v_21 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_22 : expression (bv 8)) <- eval (extract v_5 32 40);
      v_23 <- eval (add (concat (expression.bv_nat 1 0) v_21) (concat (expression.bv_nat 1 0) v_22));
      (v_24 : expression (bv 8)) <- eval (extract v_23 1 9);
      (v_25 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_26 : expression (bv 8)) <- eval (extract v_5 40 48);
      v_27 <- eval (add (concat (expression.bv_nat 1 0) v_25) (concat (expression.bv_nat 1 0) v_26));
      (v_28 : expression (bv 8)) <- eval (extract v_27 1 9);
      (v_29 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_30 : expression (bv 8)) <- eval (extract v_5 48 56);
      v_31 <- eval (add (concat (expression.bv_nat 1 0) v_29) (concat (expression.bv_nat 1 0) v_30));
      (v_32 : expression (bv 8)) <- eval (extract v_31 1 9);
      (v_33 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_34 : expression (bv 8)) <- eval (extract v_5 56 64);
      v_35 <- eval (add (concat (expression.bv_nat 1 0) v_33) (concat (expression.bv_nat 1 0) v_34));
      (v_36 : expression (bv 8)) <- eval (extract v_35 1 9);
      (v_37 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_38 : expression (bv 8)) <- eval (extract v_5 64 72);
      v_39 <- eval (add (concat (expression.bv_nat 1 0) v_37) (concat (expression.bv_nat 1 0) v_38));
      (v_40 : expression (bv 8)) <- eval (extract v_39 1 9);
      (v_41 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_42 : expression (bv 8)) <- eval (extract v_5 72 80);
      v_43 <- eval (add (concat (expression.bv_nat 1 0) v_41) (concat (expression.bv_nat 1 0) v_42));
      (v_44 : expression (bv 8)) <- eval (extract v_43 1 9);
      (v_45 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_46 : expression (bv 8)) <- eval (extract v_5 80 88);
      v_47 <- eval (add (concat (expression.bv_nat 1 0) v_45) (concat (expression.bv_nat 1 0) v_46));
      (v_48 : expression (bv 8)) <- eval (extract v_47 1 9);
      (v_49 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_50 : expression (bv 8)) <- eval (extract v_5 88 96);
      v_51 <- eval (add (concat (expression.bv_nat 1 0) v_49) (concat (expression.bv_nat 1 0) v_50));
      (v_52 : expression (bv 8)) <- eval (extract v_51 1 9);
      (v_53 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_54 : expression (bv 8)) <- eval (extract v_5 96 104);
      v_55 <- eval (add (concat (expression.bv_nat 1 0) v_53) (concat (expression.bv_nat 1 0) v_54));
      (v_56 : expression (bv 8)) <- eval (extract v_55 1 9);
      (v_57 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_58 : expression (bv 8)) <- eval (extract v_5 104 112);
      v_59 <- eval (add (concat (expression.bv_nat 1 0) v_57) (concat (expression.bv_nat 1 0) v_58));
      (v_60 : expression (bv 8)) <- eval (extract v_59 1 9);
      (v_61 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_62 : expression (bv 8)) <- eval (extract v_5 112 120);
      v_63 <- eval (add (concat (expression.bv_nat 1 0) v_61) (concat (expression.bv_nat 1 0) v_62));
      (v_64 : expression (bv 8)) <- eval (extract v_63 1 9);
      (v_65 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_66 : expression (bv 8)) <- eval (extract v_5 120 128);
      v_67 <- eval (add (concat (expression.bv_nat 1 0) v_65) (concat (expression.bv_nat 1 0) v_66));
      (v_68 : expression (bv 8)) <- eval (extract v_67 1 9);
      (v_69 : expression (bv 8)) <- eval (extract v_3 128 136);
      (v_70 : expression (bv 8)) <- eval (extract v_5 128 136);
      v_71 <- eval (add (concat (expression.bv_nat 1 0) v_69) (concat (expression.bv_nat 1 0) v_70));
      (v_72 : expression (bv 8)) <- eval (extract v_71 1 9);
      (v_73 : expression (bv 8)) <- eval (extract v_3 136 144);
      (v_74 : expression (bv 8)) <- eval (extract v_5 136 144);
      v_75 <- eval (add (concat (expression.bv_nat 1 0) v_73) (concat (expression.bv_nat 1 0) v_74));
      (v_76 : expression (bv 8)) <- eval (extract v_75 1 9);
      (v_77 : expression (bv 8)) <- eval (extract v_3 144 152);
      (v_78 : expression (bv 8)) <- eval (extract v_5 144 152);
      v_79 <- eval (add (concat (expression.bv_nat 1 0) v_77) (concat (expression.bv_nat 1 0) v_78));
      (v_80 : expression (bv 8)) <- eval (extract v_79 1 9);
      (v_81 : expression (bv 8)) <- eval (extract v_3 152 160);
      (v_82 : expression (bv 8)) <- eval (extract v_5 152 160);
      v_83 <- eval (add (concat (expression.bv_nat 1 0) v_81) (concat (expression.bv_nat 1 0) v_82));
      (v_84 : expression (bv 8)) <- eval (extract v_83 1 9);
      (v_85 : expression (bv 8)) <- eval (extract v_3 160 168);
      (v_86 : expression (bv 8)) <- eval (extract v_5 160 168);
      v_87 <- eval (add (concat (expression.bv_nat 1 0) v_85) (concat (expression.bv_nat 1 0) v_86));
      (v_88 : expression (bv 8)) <- eval (extract v_87 1 9);
      (v_89 : expression (bv 8)) <- eval (extract v_3 168 176);
      (v_90 : expression (bv 8)) <- eval (extract v_5 168 176);
      v_91 <- eval (add (concat (expression.bv_nat 1 0) v_89) (concat (expression.bv_nat 1 0) v_90));
      (v_92 : expression (bv 8)) <- eval (extract v_91 1 9);
      (v_93 : expression (bv 8)) <- eval (extract v_3 176 184);
      (v_94 : expression (bv 8)) <- eval (extract v_5 176 184);
      v_95 <- eval (add (concat (expression.bv_nat 1 0) v_93) (concat (expression.bv_nat 1 0) v_94));
      (v_96 : expression (bv 8)) <- eval (extract v_95 1 9);
      (v_97 : expression (bv 8)) <- eval (extract v_3 184 192);
      (v_98 : expression (bv 8)) <- eval (extract v_5 184 192);
      v_99 <- eval (add (concat (expression.bv_nat 1 0) v_97) (concat (expression.bv_nat 1 0) v_98));
      (v_100 : expression (bv 8)) <- eval (extract v_99 1 9);
      (v_101 : expression (bv 8)) <- eval (extract v_3 192 200);
      (v_102 : expression (bv 8)) <- eval (extract v_5 192 200);
      v_103 <- eval (add (concat (expression.bv_nat 1 0) v_101) (concat (expression.bv_nat 1 0) v_102));
      (v_104 : expression (bv 8)) <- eval (extract v_103 1 9);
      (v_105 : expression (bv 8)) <- eval (extract v_3 200 208);
      (v_106 : expression (bv 8)) <- eval (extract v_5 200 208);
      v_107 <- eval (add (concat (expression.bv_nat 1 0) v_105) (concat (expression.bv_nat 1 0) v_106));
      (v_108 : expression (bv 8)) <- eval (extract v_107 1 9);
      (v_109 : expression (bv 8)) <- eval (extract v_3 208 216);
      (v_110 : expression (bv 8)) <- eval (extract v_5 208 216);
      v_111 <- eval (add (concat (expression.bv_nat 1 0) v_109) (concat (expression.bv_nat 1 0) v_110));
      (v_112 : expression (bv 8)) <- eval (extract v_111 1 9);
      (v_113 : expression (bv 8)) <- eval (extract v_3 216 224);
      (v_114 : expression (bv 8)) <- eval (extract v_5 216 224);
      v_115 <- eval (add (concat (expression.bv_nat 1 0) v_113) (concat (expression.bv_nat 1 0) v_114));
      (v_116 : expression (bv 8)) <- eval (extract v_115 1 9);
      (v_117 : expression (bv 8)) <- eval (extract v_3 224 232);
      (v_118 : expression (bv 8)) <- eval (extract v_5 224 232);
      v_119 <- eval (add (concat (expression.bv_nat 1 0) v_117) (concat (expression.bv_nat 1 0) v_118));
      (v_120 : expression (bv 8)) <- eval (extract v_119 1 9);
      (v_121 : expression (bv 8)) <- eval (extract v_3 232 240);
      (v_122 : expression (bv 8)) <- eval (extract v_5 232 240);
      v_123 <- eval (add (concat (expression.bv_nat 1 0) v_121) (concat (expression.bv_nat 1 0) v_122));
      (v_124 : expression (bv 8)) <- eval (extract v_123 1 9);
      (v_125 : expression (bv 8)) <- eval (extract v_3 240 248);
      (v_126 : expression (bv 8)) <- eval (extract v_5 240 248);
      v_127 <- eval (add (concat (expression.bv_nat 1 0) v_125) (concat (expression.bv_nat 1 0) v_126));
      (v_128 : expression (bv 8)) <- eval (extract v_127 1 9);
      (v_129 : expression (bv 8)) <- eval (extract v_3 248 256);
      (v_130 : expression (bv 8)) <- eval (extract v_5 248 256);
      v_131 <- eval (add (concat (expression.bv_nat 1 0) v_129) (concat (expression.bv_nat 1 0) v_130));
      (v_132 : expression (bv 8)) <- eval (extract v_131 1 9);
      setRegister (lhs.of_reg ymm_2) (concat (mux (isBitSet v_7 0) (expression.bv_nat 8 255) v_8) (concat (mux (isBitSet v_11 0) (expression.bv_nat 8 255) v_12) (concat (mux (isBitSet v_15 0) (expression.bv_nat 8 255) v_16) (concat (mux (isBitSet v_19 0) (expression.bv_nat 8 255) v_20) (concat (mux (isBitSet v_23 0) (expression.bv_nat 8 255) v_24) (concat (mux (isBitSet v_27 0) (expression.bv_nat 8 255) v_28) (concat (mux (isBitSet v_31 0) (expression.bv_nat 8 255) v_32) (concat (mux (isBitSet v_35 0) (expression.bv_nat 8 255) v_36) (concat (mux (isBitSet v_39 0) (expression.bv_nat 8 255) v_40) (concat (mux (isBitSet v_43 0) (expression.bv_nat 8 255) v_44) (concat (mux (isBitSet v_47 0) (expression.bv_nat 8 255) v_48) (concat (mux (isBitSet v_51 0) (expression.bv_nat 8 255) v_52) (concat (mux (isBitSet v_55 0) (expression.bv_nat 8 255) v_56) (concat (mux (isBitSet v_59 0) (expression.bv_nat 8 255) v_60) (concat (mux (isBitSet v_63 0) (expression.bv_nat 8 255) v_64) (concat (mux (isBitSet v_67 0) (expression.bv_nat 8 255) v_68) (concat (mux (isBitSet v_71 0) (expression.bv_nat 8 255) v_72) (concat (mux (isBitSet v_75 0) (expression.bv_nat 8 255) v_76) (concat (mux (isBitSet v_79 0) (expression.bv_nat 8 255) v_80) (concat (mux (isBitSet v_83 0) (expression.bv_nat 8 255) v_84) (concat (mux (isBitSet v_87 0) (expression.bv_nat 8 255) v_88) (concat (mux (isBitSet v_91 0) (expression.bv_nat 8 255) v_92) (concat (mux (isBitSet v_95 0) (expression.bv_nat 8 255) v_96) (concat (mux (isBitSet v_99 0) (expression.bv_nat 8 255) v_100) (concat (mux (isBitSet v_103 0) (expression.bv_nat 8 255) v_104) (concat (mux (isBitSet v_107 0) (expression.bv_nat 8 255) v_108) (concat (mux (isBitSet v_111 0) (expression.bv_nat 8 255) v_112) (concat (mux (isBitSet v_115 0) (expression.bv_nat 8 255) v_116) (concat (mux (isBitSet v_119 0) (expression.bv_nat 8 255) v_120) (concat (mux (isBitSet v_123 0) (expression.bv_nat 8 255) v_124) (concat (mux (isBitSet v_127 0) (expression.bv_nat 8 255) v_128) (mux (isBitSet v_131 0) (expression.bv_nat 8 255) v_132))))))))))))))))))))))))))))))));
      pure ()
    pat_end
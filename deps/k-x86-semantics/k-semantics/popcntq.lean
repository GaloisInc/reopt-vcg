def popcntq : instruction :=
  definst "popcntq" $ do
    instr_pat $ fun (mem_0 : Mem) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 1)) <- eval (extract v_3 0 1);
      let v_5 <- eval (concat (expression.bv_nat 1 0) v_4);
      let (v_6 : expression (bv 1)) <- eval (extract v_3 1 2);
      let v_7 <- eval (concat (expression.bv_nat 1 0) v_6);
      let v_8 <- eval (concat (expression.bv_nat 2 0) (add v_5 v_7));
      let (v_9 : expression (bv 1)) <- eval (extract v_3 2 3);
      let v_10 <- eval (concat (expression.bv_nat 1 0) v_9);
      let (v_11 : expression (bv 1)) <- eval (extract v_3 3 4);
      let v_12 <- eval (concat (expression.bv_nat 1 0) v_11);
      let v_13 <- eval (concat (expression.bv_nat 2 0) (add v_10 v_12));
      let v_14 <- eval (concat (expression.bv_nat 4 0) (add v_8 v_13));
      let (v_15 : expression (bv 1)) <- eval (extract v_3 4 5);
      let v_16 <- eval (concat (expression.bv_nat 1 0) v_15);
      let (v_17 : expression (bv 1)) <- eval (extract v_3 5 6);
      let v_18 <- eval (concat (expression.bv_nat 1 0) v_17);
      let v_19 <- eval (concat (expression.bv_nat 2 0) (add v_16 v_18));
      let (v_20 : expression (bv 1)) <- eval (extract v_3 6 7);
      let v_21 <- eval (concat (expression.bv_nat 1 0) v_20);
      let (v_22 : expression (bv 1)) <- eval (extract v_3 7 8);
      let v_23 <- eval (concat (expression.bv_nat 1 0) v_22);
      let v_24 <- eval (concat (expression.bv_nat 2 0) (add v_21 v_23));
      let v_25 <- eval (concat (expression.bv_nat 4 0) (add v_19 v_24));
      let v_26 <- eval (concat (expression.bv_nat 8 0) (add v_14 v_25));
      let (v_27 : expression (bv 1)) <- eval (extract v_3 8 9);
      let v_28 <- eval (concat (expression.bv_nat 1 0) v_27);
      let (v_29 : expression (bv 1)) <- eval (extract v_3 9 10);
      let v_30 <- eval (concat (expression.bv_nat 1 0) v_29);
      let v_31 <- eval (concat (expression.bv_nat 2 0) (add v_28 v_30));
      let (v_32 : expression (bv 1)) <- eval (extract v_3 10 11);
      let v_33 <- eval (concat (expression.bv_nat 1 0) v_32);
      let (v_34 : expression (bv 1)) <- eval (extract v_3 11 12);
      let v_35 <- eval (concat (expression.bv_nat 1 0) v_34);
      let v_36 <- eval (concat (expression.bv_nat 2 0) (add v_33 v_35));
      let v_37 <- eval (concat (expression.bv_nat 4 0) (add v_31 v_36));
      let (v_38 : expression (bv 1)) <- eval (extract v_3 12 13);
      let v_39 <- eval (concat (expression.bv_nat 1 0) v_38);
      let (v_40 : expression (bv 1)) <- eval (extract v_3 13 14);
      let v_41 <- eval (concat (expression.bv_nat 1 0) v_40);
      let v_42 <- eval (concat (expression.bv_nat 2 0) (add v_39 v_41));
      let (v_43 : expression (bv 1)) <- eval (extract v_3 14 15);
      let v_44 <- eval (concat (expression.bv_nat 1 0) v_43);
      let (v_45 : expression (bv 1)) <- eval (extract v_3 15 16);
      let v_46 <- eval (concat (expression.bv_nat 1 0) v_45);
      let v_47 <- eval (concat (expression.bv_nat 2 0) (add v_44 v_46));
      let v_48 <- eval (concat (expression.bv_nat 4 0) (add v_42 v_47));
      let v_49 <- eval (concat (expression.bv_nat 8 0) (add v_37 v_48));
      let v_50 <- eval (concat (expression.bv_nat 16 0) (add v_26 v_49));
      let (v_51 : expression (bv 1)) <- eval (extract v_3 16 17);
      let v_52 <- eval (concat (expression.bv_nat 1 0) v_51);
      let (v_53 : expression (bv 1)) <- eval (extract v_3 17 18);
      let v_54 <- eval (concat (expression.bv_nat 1 0) v_53);
      let v_55 <- eval (concat (expression.bv_nat 2 0) (add v_52 v_54));
      let (v_56 : expression (bv 1)) <- eval (extract v_3 18 19);
      let v_57 <- eval (concat (expression.bv_nat 1 0) v_56);
      let (v_58 : expression (bv 1)) <- eval (extract v_3 19 20);
      let v_59 <- eval (concat (expression.bv_nat 1 0) v_58);
      let v_60 <- eval (concat (expression.bv_nat 2 0) (add v_57 v_59));
      let v_61 <- eval (concat (expression.bv_nat 4 0) (add v_55 v_60));
      let (v_62 : expression (bv 1)) <- eval (extract v_3 20 21);
      let v_63 <- eval (concat (expression.bv_nat 1 0) v_62);
      let (v_64 : expression (bv 1)) <- eval (extract v_3 21 22);
      let v_65 <- eval (concat (expression.bv_nat 1 0) v_64);
      let v_66 <- eval (concat (expression.bv_nat 2 0) (add v_63 v_65));
      let (v_67 : expression (bv 1)) <- eval (extract v_3 22 23);
      let v_68 <- eval (concat (expression.bv_nat 1 0) v_67);
      let (v_69 : expression (bv 1)) <- eval (extract v_3 23 24);
      let v_70 <- eval (concat (expression.bv_nat 1 0) v_69);
      let v_71 <- eval (concat (expression.bv_nat 2 0) (add v_68 v_70));
      let v_72 <- eval (concat (expression.bv_nat 4 0) (add v_66 v_71));
      let v_73 <- eval (concat (expression.bv_nat 8 0) (add v_61 v_72));
      let (v_74 : expression (bv 1)) <- eval (extract v_3 24 25);
      let v_75 <- eval (concat (expression.bv_nat 1 0) v_74);
      let (v_76 : expression (bv 1)) <- eval (extract v_3 25 26);
      let v_77 <- eval (concat (expression.bv_nat 1 0) v_76);
      let v_78 <- eval (concat (expression.bv_nat 2 0) (add v_75 v_77));
      let (v_79 : expression (bv 1)) <- eval (extract v_3 26 27);
      let v_80 <- eval (concat (expression.bv_nat 1 0) v_79);
      let (v_81 : expression (bv 1)) <- eval (extract v_3 27 28);
      let v_82 <- eval (concat (expression.bv_nat 1 0) v_81);
      let v_83 <- eval (concat (expression.bv_nat 2 0) (add v_80 v_82));
      let v_84 <- eval (concat (expression.bv_nat 4 0) (add v_78 v_83));
      let (v_85 : expression (bv 1)) <- eval (extract v_3 28 29);
      let v_86 <- eval (concat (expression.bv_nat 1 0) v_85);
      let (v_87 : expression (bv 1)) <- eval (extract v_3 29 30);
      let v_88 <- eval (concat (expression.bv_nat 1 0) v_87);
      let v_89 <- eval (concat (expression.bv_nat 2 0) (add v_86 v_88));
      let (v_90 : expression (bv 1)) <- eval (extract v_3 30 31);
      let v_91 <- eval (concat (expression.bv_nat 1 0) v_90);
      let (v_92 : expression (bv 1)) <- eval (extract v_3 31 32);
      let v_93 <- eval (concat (expression.bv_nat 1 0) v_92);
      let v_94 <- eval (concat (expression.bv_nat 2 0) (add v_91 v_93));
      let v_95 <- eval (concat (expression.bv_nat 4 0) (add v_89 v_94));
      let v_96 <- eval (concat (expression.bv_nat 8 0) (add v_84 v_95));
      let v_97 <- eval (concat (expression.bv_nat 16 0) (add v_73 v_96));
      let v_98 <- eval (concat (expression.bv_nat 32 0) (add v_50 v_97));
      let (v_99 : expression (bv 1)) <- eval (extract v_3 32 33);
      let v_100 <- eval (concat (expression.bv_nat 1 0) v_99);
      let (v_101 : expression (bv 1)) <- eval (extract v_3 33 34);
      let v_102 <- eval (concat (expression.bv_nat 1 0) v_101);
      let v_103 <- eval (concat (expression.bv_nat 2 0) (add v_100 v_102));
      let (v_104 : expression (bv 1)) <- eval (extract v_3 34 35);
      let v_105 <- eval (concat (expression.bv_nat 1 0) v_104);
      let (v_106 : expression (bv 1)) <- eval (extract v_3 35 36);
      let v_107 <- eval (concat (expression.bv_nat 1 0) v_106);
      let v_108 <- eval (concat (expression.bv_nat 2 0) (add v_105 v_107));
      let v_109 <- eval (concat (expression.bv_nat 4 0) (add v_103 v_108));
      let (v_110 : expression (bv 1)) <- eval (extract v_3 36 37);
      let v_111 <- eval (concat (expression.bv_nat 1 0) v_110);
      let (v_112 : expression (bv 1)) <- eval (extract v_3 37 38);
      let v_113 <- eval (concat (expression.bv_nat 1 0) v_112);
      let v_114 <- eval (concat (expression.bv_nat 2 0) (add v_111 v_113));
      let (v_115 : expression (bv 1)) <- eval (extract v_3 38 39);
      let v_116 <- eval (concat (expression.bv_nat 1 0) v_115);
      let (v_117 : expression (bv 1)) <- eval (extract v_3 39 40);
      let v_118 <- eval (concat (expression.bv_nat 1 0) v_117);
      let v_119 <- eval (concat (expression.bv_nat 2 0) (add v_116 v_118));
      let v_120 <- eval (concat (expression.bv_nat 4 0) (add v_114 v_119));
      let v_121 <- eval (concat (expression.bv_nat 8 0) (add v_109 v_120));
      let (v_122 : expression (bv 1)) <- eval (extract v_3 40 41);
      let v_123 <- eval (concat (expression.bv_nat 1 0) v_122);
      let (v_124 : expression (bv 1)) <- eval (extract v_3 41 42);
      let v_125 <- eval (concat (expression.bv_nat 1 0) v_124);
      let v_126 <- eval (concat (expression.bv_nat 2 0) (add v_123 v_125));
      let (v_127 : expression (bv 1)) <- eval (extract v_3 42 43);
      let v_128 <- eval (concat (expression.bv_nat 1 0) v_127);
      let (v_129 : expression (bv 1)) <- eval (extract v_3 43 44);
      let v_130 <- eval (concat (expression.bv_nat 1 0) v_129);
      let v_131 <- eval (concat (expression.bv_nat 2 0) (add v_128 v_130));
      let v_132 <- eval (concat (expression.bv_nat 4 0) (add v_126 v_131));
      let (v_133 : expression (bv 1)) <- eval (extract v_3 44 45);
      let v_134 <- eval (concat (expression.bv_nat 1 0) v_133);
      let (v_135 : expression (bv 1)) <- eval (extract v_3 45 46);
      let v_136 <- eval (concat (expression.bv_nat 1 0) v_135);
      let v_137 <- eval (concat (expression.bv_nat 2 0) (add v_134 v_136));
      let (v_138 : expression (bv 1)) <- eval (extract v_3 46 47);
      let v_139 <- eval (concat (expression.bv_nat 1 0) v_138);
      let (v_140 : expression (bv 1)) <- eval (extract v_3 47 48);
      let v_141 <- eval (concat (expression.bv_nat 1 0) v_140);
      let v_142 <- eval (concat (expression.bv_nat 2 0) (add v_139 v_141));
      let v_143 <- eval (concat (expression.bv_nat 4 0) (add v_137 v_142));
      let v_144 <- eval (concat (expression.bv_nat 8 0) (add v_132 v_143));
      let v_145 <- eval (concat (expression.bv_nat 16 0) (add v_121 v_144));
      let (v_146 : expression (bv 1)) <- eval (extract v_3 48 49);
      let v_147 <- eval (concat (expression.bv_nat 1 0) v_146);
      let (v_148 : expression (bv 1)) <- eval (extract v_3 49 50);
      let v_149 <- eval (concat (expression.bv_nat 1 0) v_148);
      let v_150 <- eval (concat (expression.bv_nat 2 0) (add v_147 v_149));
      let (v_151 : expression (bv 1)) <- eval (extract v_3 50 51);
      let v_152 <- eval (concat (expression.bv_nat 1 0) v_151);
      let (v_153 : expression (bv 1)) <- eval (extract v_3 51 52);
      let v_154 <- eval (concat (expression.bv_nat 1 0) v_153);
      let v_155 <- eval (concat (expression.bv_nat 2 0) (add v_152 v_154));
      let v_156 <- eval (concat (expression.bv_nat 4 0) (add v_150 v_155));
      let (v_157 : expression (bv 1)) <- eval (extract v_3 52 53);
      let v_158 <- eval (concat (expression.bv_nat 1 0) v_157);
      let (v_159 : expression (bv 1)) <- eval (extract v_3 53 54);
      let v_160 <- eval (concat (expression.bv_nat 1 0) v_159);
      let v_161 <- eval (concat (expression.bv_nat 2 0) (add v_158 v_160));
      let (v_162 : expression (bv 1)) <- eval (extract v_3 54 55);
      let v_163 <- eval (concat (expression.bv_nat 1 0) v_162);
      let (v_164 : expression (bv 1)) <- eval (extract v_3 55 56);
      let v_165 <- eval (concat (expression.bv_nat 1 0) v_164);
      let v_166 <- eval (concat (expression.bv_nat 2 0) (add v_163 v_165));
      let v_167 <- eval (concat (expression.bv_nat 4 0) (add v_161 v_166));
      let v_168 <- eval (concat (expression.bv_nat 8 0) (add v_156 v_167));
      let (v_169 : expression (bv 1)) <- eval (extract v_3 56 57);
      let v_170 <- eval (concat (expression.bv_nat 1 0) v_169);
      let (v_171 : expression (bv 1)) <- eval (extract v_3 57 58);
      let v_172 <- eval (concat (expression.bv_nat 1 0) v_171);
      let v_173 <- eval (concat (expression.bv_nat 2 0) (add v_170 v_172));
      let (v_174 : expression (bv 1)) <- eval (extract v_3 58 59);
      let v_175 <- eval (concat (expression.bv_nat 1 0) v_174);
      let (v_176 : expression (bv 1)) <- eval (extract v_3 59 60);
      let v_177 <- eval (concat (expression.bv_nat 1 0) v_176);
      let v_178 <- eval (concat (expression.bv_nat 2 0) (add v_175 v_177));
      let v_179 <- eval (concat (expression.bv_nat 4 0) (add v_173 v_178));
      let (v_180 : expression (bv 1)) <- eval (extract v_3 60 61);
      let v_181 <- eval (concat (expression.bv_nat 1 0) v_180);
      let (v_182 : expression (bv 1)) <- eval (extract v_3 61 62);
      let v_183 <- eval (concat (expression.bv_nat 1 0) v_182);
      let v_184 <- eval (concat (expression.bv_nat 2 0) (add v_181 v_183));
      let (v_185 : expression (bv 1)) <- eval (extract v_3 62 63);
      let v_186 <- eval (concat (expression.bv_nat 1 0) v_185);
      let (v_187 : expression (bv 1)) <- eval (extract v_3 63 64);
      let v_188 <- eval (concat (expression.bv_nat 1 0) v_187);
      let v_189 <- eval (concat (expression.bv_nat 2 0) (add v_186 v_188));
      let v_190 <- eval (concat (expression.bv_nat 4 0) (add v_184 v_189));
      let v_191 <- eval (concat (expression.bv_nat 8 0) (add v_179 v_190));
      let v_192 <- eval (concat (expression.bv_nat 16 0) (add v_168 v_191));
      let v_193 <- eval (concat (expression.bv_nat 32 0) (add v_145 v_192));
      setRegister (lhs.of_reg r64_1) (add v_98 v_193);
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_3);
      pure ()
     action;
    instr_pat $ fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg r64_0);
      let (v_3 : expression (bv 1)) <- eval (extract v_2 0 1);
      let v_4 <- eval (concat (expression.bv_nat 1 0) v_3);
      let (v_5 : expression (bv 1)) <- eval (extract v_2 1 2);
      let v_6 <- eval (concat (expression.bv_nat 1 0) v_5);
      let v_7 <- eval (concat (expression.bv_nat 2 0) (add v_4 v_6));
      let (v_8 : expression (bv 1)) <- eval (extract v_2 2 3);
      let v_9 <- eval (concat (expression.bv_nat 1 0) v_8);
      let (v_10 : expression (bv 1)) <- eval (extract v_2 3 4);
      let v_11 <- eval (concat (expression.bv_nat 1 0) v_10);
      let v_12 <- eval (concat (expression.bv_nat 2 0) (add v_9 v_11));
      let v_13 <- eval (concat (expression.bv_nat 4 0) (add v_7 v_12));
      let (v_14 : expression (bv 1)) <- eval (extract v_2 4 5);
      let v_15 <- eval (concat (expression.bv_nat 1 0) v_14);
      let (v_16 : expression (bv 1)) <- eval (extract v_2 5 6);
      let v_17 <- eval (concat (expression.bv_nat 1 0) v_16);
      let v_18 <- eval (concat (expression.bv_nat 2 0) (add v_15 v_17));
      let (v_19 : expression (bv 1)) <- eval (extract v_2 6 7);
      let v_20 <- eval (concat (expression.bv_nat 1 0) v_19);
      let (v_21 : expression (bv 1)) <- eval (extract v_2 7 8);
      let v_22 <- eval (concat (expression.bv_nat 1 0) v_21);
      let v_23 <- eval (concat (expression.bv_nat 2 0) (add v_20 v_22));
      let v_24 <- eval (concat (expression.bv_nat 4 0) (add v_18 v_23));
      let v_25 <- eval (concat (expression.bv_nat 8 0) (add v_13 v_24));
      let (v_26 : expression (bv 1)) <- eval (extract v_2 8 9);
      let v_27 <- eval (concat (expression.bv_nat 1 0) v_26);
      let (v_28 : expression (bv 1)) <- eval (extract v_2 9 10);
      let v_29 <- eval (concat (expression.bv_nat 1 0) v_28);
      let v_30 <- eval (concat (expression.bv_nat 2 0) (add v_27 v_29));
      let (v_31 : expression (bv 1)) <- eval (extract v_2 10 11);
      let v_32 <- eval (concat (expression.bv_nat 1 0) v_31);
      let (v_33 : expression (bv 1)) <- eval (extract v_2 11 12);
      let v_34 <- eval (concat (expression.bv_nat 1 0) v_33);
      let v_35 <- eval (concat (expression.bv_nat 2 0) (add v_32 v_34));
      let v_36 <- eval (concat (expression.bv_nat 4 0) (add v_30 v_35));
      let (v_37 : expression (bv 1)) <- eval (extract v_2 12 13);
      let v_38 <- eval (concat (expression.bv_nat 1 0) v_37);
      let (v_39 : expression (bv 1)) <- eval (extract v_2 13 14);
      let v_40 <- eval (concat (expression.bv_nat 1 0) v_39);
      let v_41 <- eval (concat (expression.bv_nat 2 0) (add v_38 v_40));
      let (v_42 : expression (bv 1)) <- eval (extract v_2 14 15);
      let v_43 <- eval (concat (expression.bv_nat 1 0) v_42);
      let (v_44 : expression (bv 1)) <- eval (extract v_2 15 16);
      let v_45 <- eval (concat (expression.bv_nat 1 0) v_44);
      let v_46 <- eval (concat (expression.bv_nat 2 0) (add v_43 v_45));
      let v_47 <- eval (concat (expression.bv_nat 4 0) (add v_41 v_46));
      let v_48 <- eval (concat (expression.bv_nat 8 0) (add v_36 v_47));
      let v_49 <- eval (concat (expression.bv_nat 16 0) (add v_25 v_48));
      let (v_50 : expression (bv 1)) <- eval (extract v_2 16 17);
      let v_51 <- eval (concat (expression.bv_nat 1 0) v_50);
      let (v_52 : expression (bv 1)) <- eval (extract v_2 17 18);
      let v_53 <- eval (concat (expression.bv_nat 1 0) v_52);
      let v_54 <- eval (concat (expression.bv_nat 2 0) (add v_51 v_53));
      let (v_55 : expression (bv 1)) <- eval (extract v_2 18 19);
      let v_56 <- eval (concat (expression.bv_nat 1 0) v_55);
      let (v_57 : expression (bv 1)) <- eval (extract v_2 19 20);
      let v_58 <- eval (concat (expression.bv_nat 1 0) v_57);
      let v_59 <- eval (concat (expression.bv_nat 2 0) (add v_56 v_58));
      let v_60 <- eval (concat (expression.bv_nat 4 0) (add v_54 v_59));
      let (v_61 : expression (bv 1)) <- eval (extract v_2 20 21);
      let v_62 <- eval (concat (expression.bv_nat 1 0) v_61);
      let (v_63 : expression (bv 1)) <- eval (extract v_2 21 22);
      let v_64 <- eval (concat (expression.bv_nat 1 0) v_63);
      let v_65 <- eval (concat (expression.bv_nat 2 0) (add v_62 v_64));
      let (v_66 : expression (bv 1)) <- eval (extract v_2 22 23);
      let v_67 <- eval (concat (expression.bv_nat 1 0) v_66);
      let (v_68 : expression (bv 1)) <- eval (extract v_2 23 24);
      let v_69 <- eval (concat (expression.bv_nat 1 0) v_68);
      let v_70 <- eval (concat (expression.bv_nat 2 0) (add v_67 v_69));
      let v_71 <- eval (concat (expression.bv_nat 4 0) (add v_65 v_70));
      let v_72 <- eval (concat (expression.bv_nat 8 0) (add v_60 v_71));
      let (v_73 : expression (bv 1)) <- eval (extract v_2 24 25);
      let v_74 <- eval (concat (expression.bv_nat 1 0) v_73);
      let (v_75 : expression (bv 1)) <- eval (extract v_2 25 26);
      let v_76 <- eval (concat (expression.bv_nat 1 0) v_75);
      let v_77 <- eval (concat (expression.bv_nat 2 0) (add v_74 v_76));
      let (v_78 : expression (bv 1)) <- eval (extract v_2 26 27);
      let v_79 <- eval (concat (expression.bv_nat 1 0) v_78);
      let (v_80 : expression (bv 1)) <- eval (extract v_2 27 28);
      let v_81 <- eval (concat (expression.bv_nat 1 0) v_80);
      let v_82 <- eval (concat (expression.bv_nat 2 0) (add v_79 v_81));
      let v_83 <- eval (concat (expression.bv_nat 4 0) (add v_77 v_82));
      let (v_84 : expression (bv 1)) <- eval (extract v_2 28 29);
      let v_85 <- eval (concat (expression.bv_nat 1 0) v_84);
      let (v_86 : expression (bv 1)) <- eval (extract v_2 29 30);
      let v_87 <- eval (concat (expression.bv_nat 1 0) v_86);
      let v_88 <- eval (concat (expression.bv_nat 2 0) (add v_85 v_87));
      let (v_89 : expression (bv 1)) <- eval (extract v_2 30 31);
      let v_90 <- eval (concat (expression.bv_nat 1 0) v_89);
      let (v_91 : expression (bv 1)) <- eval (extract v_2 31 32);
      let v_92 <- eval (concat (expression.bv_nat 1 0) v_91);
      let v_93 <- eval (concat (expression.bv_nat 2 0) (add v_90 v_92));
      let v_94 <- eval (concat (expression.bv_nat 4 0) (add v_88 v_93));
      let v_95 <- eval (concat (expression.bv_nat 8 0) (add v_83 v_94));
      let v_96 <- eval (concat (expression.bv_nat 16 0) (add v_72 v_95));
      let v_97 <- eval (concat (expression.bv_nat 32 0) (add v_49 v_96));
      let (v_98 : expression (bv 1)) <- eval (extract v_2 32 33);
      let v_99 <- eval (concat (expression.bv_nat 1 0) v_98);
      let (v_100 : expression (bv 1)) <- eval (extract v_2 33 34);
      let v_101 <- eval (concat (expression.bv_nat 1 0) v_100);
      let v_102 <- eval (concat (expression.bv_nat 2 0) (add v_99 v_101));
      let (v_103 : expression (bv 1)) <- eval (extract v_2 34 35);
      let v_104 <- eval (concat (expression.bv_nat 1 0) v_103);
      let (v_105 : expression (bv 1)) <- eval (extract v_2 35 36);
      let v_106 <- eval (concat (expression.bv_nat 1 0) v_105);
      let v_107 <- eval (concat (expression.bv_nat 2 0) (add v_104 v_106));
      let v_108 <- eval (concat (expression.bv_nat 4 0) (add v_102 v_107));
      let (v_109 : expression (bv 1)) <- eval (extract v_2 36 37);
      let v_110 <- eval (concat (expression.bv_nat 1 0) v_109);
      let (v_111 : expression (bv 1)) <- eval (extract v_2 37 38);
      let v_112 <- eval (concat (expression.bv_nat 1 0) v_111);
      let v_113 <- eval (concat (expression.bv_nat 2 0) (add v_110 v_112));
      let (v_114 : expression (bv 1)) <- eval (extract v_2 38 39);
      let v_115 <- eval (concat (expression.bv_nat 1 0) v_114);
      let (v_116 : expression (bv 1)) <- eval (extract v_2 39 40);
      let v_117 <- eval (concat (expression.bv_nat 1 0) v_116);
      let v_118 <- eval (concat (expression.bv_nat 2 0) (add v_115 v_117));
      let v_119 <- eval (concat (expression.bv_nat 4 0) (add v_113 v_118));
      let v_120 <- eval (concat (expression.bv_nat 8 0) (add v_108 v_119));
      let (v_121 : expression (bv 1)) <- eval (extract v_2 40 41);
      let v_122 <- eval (concat (expression.bv_nat 1 0) v_121);
      let (v_123 : expression (bv 1)) <- eval (extract v_2 41 42);
      let v_124 <- eval (concat (expression.bv_nat 1 0) v_123);
      let v_125 <- eval (concat (expression.bv_nat 2 0) (add v_122 v_124));
      let (v_126 : expression (bv 1)) <- eval (extract v_2 42 43);
      let v_127 <- eval (concat (expression.bv_nat 1 0) v_126);
      let (v_128 : expression (bv 1)) <- eval (extract v_2 43 44);
      let v_129 <- eval (concat (expression.bv_nat 1 0) v_128);
      let v_130 <- eval (concat (expression.bv_nat 2 0) (add v_127 v_129));
      let v_131 <- eval (concat (expression.bv_nat 4 0) (add v_125 v_130));
      let (v_132 : expression (bv 1)) <- eval (extract v_2 44 45);
      let v_133 <- eval (concat (expression.bv_nat 1 0) v_132);
      let (v_134 : expression (bv 1)) <- eval (extract v_2 45 46);
      let v_135 <- eval (concat (expression.bv_nat 1 0) v_134);
      let v_136 <- eval (concat (expression.bv_nat 2 0) (add v_133 v_135));
      let (v_137 : expression (bv 1)) <- eval (extract v_2 46 47);
      let v_138 <- eval (concat (expression.bv_nat 1 0) v_137);
      let (v_139 : expression (bv 1)) <- eval (extract v_2 47 48);
      let v_140 <- eval (concat (expression.bv_nat 1 0) v_139);
      let v_141 <- eval (concat (expression.bv_nat 2 0) (add v_138 v_140));
      let v_142 <- eval (concat (expression.bv_nat 4 0) (add v_136 v_141));
      let v_143 <- eval (concat (expression.bv_nat 8 0) (add v_131 v_142));
      let v_144 <- eval (concat (expression.bv_nat 16 0) (add v_120 v_143));
      let (v_145 : expression (bv 1)) <- eval (extract v_2 48 49);
      let v_146 <- eval (concat (expression.bv_nat 1 0) v_145);
      let (v_147 : expression (bv 1)) <- eval (extract v_2 49 50);
      let v_148 <- eval (concat (expression.bv_nat 1 0) v_147);
      let v_149 <- eval (concat (expression.bv_nat 2 0) (add v_146 v_148));
      let (v_150 : expression (bv 1)) <- eval (extract v_2 50 51);
      let v_151 <- eval (concat (expression.bv_nat 1 0) v_150);
      let (v_152 : expression (bv 1)) <- eval (extract v_2 51 52);
      let v_153 <- eval (concat (expression.bv_nat 1 0) v_152);
      let v_154 <- eval (concat (expression.bv_nat 2 0) (add v_151 v_153));
      let v_155 <- eval (concat (expression.bv_nat 4 0) (add v_149 v_154));
      let (v_156 : expression (bv 1)) <- eval (extract v_2 52 53);
      let v_157 <- eval (concat (expression.bv_nat 1 0) v_156);
      let (v_158 : expression (bv 1)) <- eval (extract v_2 53 54);
      let v_159 <- eval (concat (expression.bv_nat 1 0) v_158);
      let v_160 <- eval (concat (expression.bv_nat 2 0) (add v_157 v_159));
      let (v_161 : expression (bv 1)) <- eval (extract v_2 54 55);
      let v_162 <- eval (concat (expression.bv_nat 1 0) v_161);
      let (v_163 : expression (bv 1)) <- eval (extract v_2 55 56);
      let v_164 <- eval (concat (expression.bv_nat 1 0) v_163);
      let v_165 <- eval (concat (expression.bv_nat 2 0) (add v_162 v_164));
      let v_166 <- eval (concat (expression.bv_nat 4 0) (add v_160 v_165));
      let v_167 <- eval (concat (expression.bv_nat 8 0) (add v_155 v_166));
      let (v_168 : expression (bv 1)) <- eval (extract v_2 56 57);
      let v_169 <- eval (concat (expression.bv_nat 1 0) v_168);
      let (v_170 : expression (bv 1)) <- eval (extract v_2 57 58);
      let v_171 <- eval (concat (expression.bv_nat 1 0) v_170);
      let v_172 <- eval (concat (expression.bv_nat 2 0) (add v_169 v_171));
      let (v_173 : expression (bv 1)) <- eval (extract v_2 58 59);
      let v_174 <- eval (concat (expression.bv_nat 1 0) v_173);
      let (v_175 : expression (bv 1)) <- eval (extract v_2 59 60);
      let v_176 <- eval (concat (expression.bv_nat 1 0) v_175);
      let v_177 <- eval (concat (expression.bv_nat 2 0) (add v_174 v_176));
      let v_178 <- eval (concat (expression.bv_nat 4 0) (add v_172 v_177));
      let (v_179 : expression (bv 1)) <- eval (extract v_2 60 61);
      let v_180 <- eval (concat (expression.bv_nat 1 0) v_179);
      let (v_181 : expression (bv 1)) <- eval (extract v_2 61 62);
      let v_182 <- eval (concat (expression.bv_nat 1 0) v_181);
      let v_183 <- eval (concat (expression.bv_nat 2 0) (add v_180 v_182));
      let (v_184 : expression (bv 1)) <- eval (extract v_2 62 63);
      let v_185 <- eval (concat (expression.bv_nat 1 0) v_184);
      let (v_186 : expression (bv 1)) <- eval (extract v_2 63 64);
      let v_187 <- eval (concat (expression.bv_nat 1 0) v_186);
      let v_188 <- eval (concat (expression.bv_nat 2 0) (add v_185 v_187));
      let v_189 <- eval (concat (expression.bv_nat 4 0) (add v_183 v_188));
      let v_190 <- eval (concat (expression.bv_nat 8 0) (add v_178 v_189));
      let v_191 <- eval (concat (expression.bv_nat 16 0) (add v_167 v_190));
      let v_192 <- eval (concat (expression.bv_nat 32 0) (add v_144 v_191));
      setRegister (lhs.of_reg r64_1) (add v_97 v_192);
      setRegister af bit_zero;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf bit_zero;
      setRegister sf bit_zero;
      setRegister zf (zeroFlag v_2);
      pure ()
     action

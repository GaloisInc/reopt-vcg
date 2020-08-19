def vpmaddubsw : instruction :=
  definst "vpmaddubsw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      (v_5 : expression (bv 8)) <- eval (extract v_4 8 16);
      v_6 <- getRegister (lhs.of_reg xmm_1);
      (v_7 : expression (bv 8)) <- eval (extract v_6 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_4 0 8);
      (v_9 : expression (bv 8)) <- eval (extract v_6 0 8);
      v_10 <- eval (add (sext (mul (sext v_5 16) (concat (expression.bv_nat 8 0) v_7)) 32) (sext (mul (sext v_8 16) (concat (expression.bv_nat 8 0) v_9)) 32));
      (v_11 : expression (bv 16)) <- eval (extract v_10 16 32);
      (v_12 : expression (bv 8)) <- eval (extract v_4 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_6 24 32);
      (v_14 : expression (bv 8)) <- eval (extract v_4 16 24);
      (v_15 : expression (bv 8)) <- eval (extract v_6 16 24);
      v_16 <- eval (add (sext (mul (sext v_12 16) (concat (expression.bv_nat 8 0) v_13)) 32) (sext (mul (sext v_14 16) (concat (expression.bv_nat 8 0) v_15)) 32));
      (v_17 : expression (bv 16)) <- eval (extract v_16 16 32);
      (v_18 : expression (bv 8)) <- eval (extract v_4 40 48);
      (v_19 : expression (bv 8)) <- eval (extract v_6 40 48);
      (v_20 : expression (bv 8)) <- eval (extract v_4 32 40);
      (v_21 : expression (bv 8)) <- eval (extract v_6 32 40);
      v_22 <- eval (add (sext (mul (sext v_18 16) (concat (expression.bv_nat 8 0) v_19)) 32) (sext (mul (sext v_20 16) (concat (expression.bv_nat 8 0) v_21)) 32));
      (v_23 : expression (bv 16)) <- eval (extract v_22 16 32);
      (v_24 : expression (bv 8)) <- eval (extract v_4 56 64);
      (v_25 : expression (bv 8)) <- eval (extract v_6 56 64);
      (v_26 : expression (bv 8)) <- eval (extract v_4 48 56);
      (v_27 : expression (bv 8)) <- eval (extract v_6 48 56);
      v_28 <- eval (add (sext (mul (sext v_24 16) (concat (expression.bv_nat 8 0) v_25)) 32) (sext (mul (sext v_26 16) (concat (expression.bv_nat 8 0) v_27)) 32));
      (v_29 : expression (bv 16)) <- eval (extract v_28 16 32);
      (v_30 : expression (bv 8)) <- eval (extract v_4 72 80);
      (v_31 : expression (bv 8)) <- eval (extract v_6 72 80);
      (v_32 : expression (bv 8)) <- eval (extract v_4 64 72);
      (v_33 : expression (bv 8)) <- eval (extract v_6 64 72);
      v_34 <- eval (add (sext (mul (sext v_30 16) (concat (expression.bv_nat 8 0) v_31)) 32) (sext (mul (sext v_32 16) (concat (expression.bv_nat 8 0) v_33)) 32));
      (v_35 : expression (bv 16)) <- eval (extract v_34 16 32);
      (v_36 : expression (bv 8)) <- eval (extract v_4 88 96);
      (v_37 : expression (bv 8)) <- eval (extract v_6 88 96);
      (v_38 : expression (bv 8)) <- eval (extract v_4 80 88);
      (v_39 : expression (bv 8)) <- eval (extract v_6 80 88);
      v_40 <- eval (add (sext (mul (sext v_36 16) (concat (expression.bv_nat 8 0) v_37)) 32) (sext (mul (sext v_38 16) (concat (expression.bv_nat 8 0) v_39)) 32));
      (v_41 : expression (bv 16)) <- eval (extract v_40 16 32);
      (v_42 : expression (bv 8)) <- eval (extract v_4 104 112);
      (v_43 : expression (bv 8)) <- eval (extract v_6 104 112);
      (v_44 : expression (bv 8)) <- eval (extract v_4 96 104);
      (v_45 : expression (bv 8)) <- eval (extract v_6 96 104);
      v_46 <- eval (add (sext (mul (sext v_42 16) (concat (expression.bv_nat 8 0) v_43)) 32) (sext (mul (sext v_44 16) (concat (expression.bv_nat 8 0) v_45)) 32));
      (v_47 : expression (bv 16)) <- eval (extract v_46 16 32);
      (v_48 : expression (bv 8)) <- eval (extract v_4 120 128);
      (v_49 : expression (bv 8)) <- eval (extract v_6 120 128);
      (v_50 : expression (bv 8)) <- eval (extract v_4 112 120);
      (v_51 : expression (bv 8)) <- eval (extract v_6 112 120);
      v_52 <- eval (add (sext (mul (sext v_48 16) (concat (expression.bv_nat 8 0) v_49)) 32) (sext (mul (sext v_50 16) (concat (expression.bv_nat 8 0) v_51)) 32));
      (v_53 : expression (bv 16)) <- eval (extract v_52 16 32);
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_11)) (concat (mux (sgt v_16 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_16 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_17)) (concat (mux (sgt v_22 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_22 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_23)) (concat (mux (sgt v_28 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_28 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_29)) (concat (mux (sgt v_34 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_34 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_35)) (concat (mux (sgt v_40 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_40 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_41)) (concat (mux (sgt v_46 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_46 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_47)) (mux (sgt v_52 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_52 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_53)))))))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      (v_5 : expression (bv 8)) <- eval (extract v_4 8 16);
      v_6 <- getRegister (lhs.of_reg ymm_1);
      (v_7 : expression (bv 8)) <- eval (extract v_6 8 16);
      (v_8 : expression (bv 8)) <- eval (extract v_4 0 8);
      (v_9 : expression (bv 8)) <- eval (extract v_6 0 8);
      v_10 <- eval (add (sext (mul (sext v_5 16) (concat (expression.bv_nat 8 0) v_7)) 32) (sext (mul (sext v_8 16) (concat (expression.bv_nat 8 0) v_9)) 32));
      (v_11 : expression (bv 16)) <- eval (extract v_10 16 32);
      (v_12 : expression (bv 8)) <- eval (extract v_4 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_6 24 32);
      (v_14 : expression (bv 8)) <- eval (extract v_4 16 24);
      (v_15 : expression (bv 8)) <- eval (extract v_6 16 24);
      v_16 <- eval (add (sext (mul (sext v_12 16) (concat (expression.bv_nat 8 0) v_13)) 32) (sext (mul (sext v_14 16) (concat (expression.bv_nat 8 0) v_15)) 32));
      (v_17 : expression (bv 16)) <- eval (extract v_16 16 32);
      (v_18 : expression (bv 8)) <- eval (extract v_4 40 48);
      (v_19 : expression (bv 8)) <- eval (extract v_6 40 48);
      (v_20 : expression (bv 8)) <- eval (extract v_4 32 40);
      (v_21 : expression (bv 8)) <- eval (extract v_6 32 40);
      v_22 <- eval (add (sext (mul (sext v_18 16) (concat (expression.bv_nat 8 0) v_19)) 32) (sext (mul (sext v_20 16) (concat (expression.bv_nat 8 0) v_21)) 32));
      (v_23 : expression (bv 16)) <- eval (extract v_22 16 32);
      (v_24 : expression (bv 8)) <- eval (extract v_4 56 64);
      (v_25 : expression (bv 8)) <- eval (extract v_6 56 64);
      (v_26 : expression (bv 8)) <- eval (extract v_4 48 56);
      (v_27 : expression (bv 8)) <- eval (extract v_6 48 56);
      v_28 <- eval (add (sext (mul (sext v_24 16) (concat (expression.bv_nat 8 0) v_25)) 32) (sext (mul (sext v_26 16) (concat (expression.bv_nat 8 0) v_27)) 32));
      (v_29 : expression (bv 16)) <- eval (extract v_28 16 32);
      (v_30 : expression (bv 8)) <- eval (extract v_4 72 80);
      (v_31 : expression (bv 8)) <- eval (extract v_6 72 80);
      (v_32 : expression (bv 8)) <- eval (extract v_4 64 72);
      (v_33 : expression (bv 8)) <- eval (extract v_6 64 72);
      v_34 <- eval (add (sext (mul (sext v_30 16) (concat (expression.bv_nat 8 0) v_31)) 32) (sext (mul (sext v_32 16) (concat (expression.bv_nat 8 0) v_33)) 32));
      (v_35 : expression (bv 16)) <- eval (extract v_34 16 32);
      (v_36 : expression (bv 8)) <- eval (extract v_4 88 96);
      (v_37 : expression (bv 8)) <- eval (extract v_6 88 96);
      (v_38 : expression (bv 8)) <- eval (extract v_4 80 88);
      (v_39 : expression (bv 8)) <- eval (extract v_6 80 88);
      v_40 <- eval (add (sext (mul (sext v_36 16) (concat (expression.bv_nat 8 0) v_37)) 32) (sext (mul (sext v_38 16) (concat (expression.bv_nat 8 0) v_39)) 32));
      (v_41 : expression (bv 16)) <- eval (extract v_40 16 32);
      (v_42 : expression (bv 8)) <- eval (extract v_4 104 112);
      (v_43 : expression (bv 8)) <- eval (extract v_6 104 112);
      (v_44 : expression (bv 8)) <- eval (extract v_4 96 104);
      (v_45 : expression (bv 8)) <- eval (extract v_6 96 104);
      v_46 <- eval (add (sext (mul (sext v_42 16) (concat (expression.bv_nat 8 0) v_43)) 32) (sext (mul (sext v_44 16) (concat (expression.bv_nat 8 0) v_45)) 32));
      (v_47 : expression (bv 16)) <- eval (extract v_46 16 32);
      (v_48 : expression (bv 8)) <- eval (extract v_4 120 128);
      (v_49 : expression (bv 8)) <- eval (extract v_6 120 128);
      (v_50 : expression (bv 8)) <- eval (extract v_4 112 120);
      (v_51 : expression (bv 8)) <- eval (extract v_6 112 120);
      v_52 <- eval (add (sext (mul (sext v_48 16) (concat (expression.bv_nat 8 0) v_49)) 32) (sext (mul (sext v_50 16) (concat (expression.bv_nat 8 0) v_51)) 32));
      (v_53 : expression (bv 16)) <- eval (extract v_52 16 32);
      (v_54 : expression (bv 8)) <- eval (extract v_4 136 144);
      (v_55 : expression (bv 8)) <- eval (extract v_6 136 144);
      (v_56 : expression (bv 8)) <- eval (extract v_4 128 136);
      (v_57 : expression (bv 8)) <- eval (extract v_6 128 136);
      v_58 <- eval (add (sext (mul (sext v_54 16) (concat (expression.bv_nat 8 0) v_55)) 32) (sext (mul (sext v_56 16) (concat (expression.bv_nat 8 0) v_57)) 32));
      (v_59 : expression (bv 16)) <- eval (extract v_58 16 32);
      (v_60 : expression (bv 8)) <- eval (extract v_4 152 160);
      (v_61 : expression (bv 8)) <- eval (extract v_6 152 160);
      (v_62 : expression (bv 8)) <- eval (extract v_4 144 152);
      (v_63 : expression (bv 8)) <- eval (extract v_6 144 152);
      v_64 <- eval (add (sext (mul (sext v_60 16) (concat (expression.bv_nat 8 0) v_61)) 32) (sext (mul (sext v_62 16) (concat (expression.bv_nat 8 0) v_63)) 32));
      (v_65 : expression (bv 16)) <- eval (extract v_64 16 32);
      (v_66 : expression (bv 8)) <- eval (extract v_4 168 176);
      (v_67 : expression (bv 8)) <- eval (extract v_6 168 176);
      (v_68 : expression (bv 8)) <- eval (extract v_4 160 168);
      (v_69 : expression (bv 8)) <- eval (extract v_6 160 168);
      v_70 <- eval (add (sext (mul (sext v_66 16) (concat (expression.bv_nat 8 0) v_67)) 32) (sext (mul (sext v_68 16) (concat (expression.bv_nat 8 0) v_69)) 32));
      (v_71 : expression (bv 16)) <- eval (extract v_70 16 32);
      (v_72 : expression (bv 8)) <- eval (extract v_4 184 192);
      (v_73 : expression (bv 8)) <- eval (extract v_6 184 192);
      (v_74 : expression (bv 8)) <- eval (extract v_4 176 184);
      (v_75 : expression (bv 8)) <- eval (extract v_6 176 184);
      v_76 <- eval (add (sext (mul (sext v_72 16) (concat (expression.bv_nat 8 0) v_73)) 32) (sext (mul (sext v_74 16) (concat (expression.bv_nat 8 0) v_75)) 32));
      (v_77 : expression (bv 16)) <- eval (extract v_76 16 32);
      (v_78 : expression (bv 8)) <- eval (extract v_4 200 208);
      (v_79 : expression (bv 8)) <- eval (extract v_6 200 208);
      (v_80 : expression (bv 8)) <- eval (extract v_4 192 200);
      (v_81 : expression (bv 8)) <- eval (extract v_6 192 200);
      v_82 <- eval (add (sext (mul (sext v_78 16) (concat (expression.bv_nat 8 0) v_79)) 32) (sext (mul (sext v_80 16) (concat (expression.bv_nat 8 0) v_81)) 32));
      (v_83 : expression (bv 16)) <- eval (extract v_82 16 32);
      (v_84 : expression (bv 8)) <- eval (extract v_4 216 224);
      (v_85 : expression (bv 8)) <- eval (extract v_6 216 224);
      (v_86 : expression (bv 8)) <- eval (extract v_4 208 216);
      (v_87 : expression (bv 8)) <- eval (extract v_6 208 216);
      v_88 <- eval (add (sext (mul (sext v_84 16) (concat (expression.bv_nat 8 0) v_85)) 32) (sext (mul (sext v_86 16) (concat (expression.bv_nat 8 0) v_87)) 32));
      (v_89 : expression (bv 16)) <- eval (extract v_88 16 32);
      (v_90 : expression (bv 8)) <- eval (extract v_4 232 240);
      (v_91 : expression (bv 8)) <- eval (extract v_6 232 240);
      (v_92 : expression (bv 8)) <- eval (extract v_4 224 232);
      (v_93 : expression (bv 8)) <- eval (extract v_6 224 232);
      v_94 <- eval (add (sext (mul (sext v_90 16) (concat (expression.bv_nat 8 0) v_91)) 32) (sext (mul (sext v_92 16) (concat (expression.bv_nat 8 0) v_93)) 32));
      (v_95 : expression (bv 16)) <- eval (extract v_94 16 32);
      (v_96 : expression (bv 8)) <- eval (extract v_4 248 256);
      (v_97 : expression (bv 8)) <- eval (extract v_6 248 256);
      (v_98 : expression (bv 8)) <- eval (extract v_4 240 248);
      (v_99 : expression (bv 8)) <- eval (extract v_6 240 248);
      v_100 <- eval (add (sext (mul (sext v_96 16) (concat (expression.bv_nat 8 0) v_97)) 32) (sext (mul (sext v_98 16) (concat (expression.bv_nat 8 0) v_99)) 32));
      (v_101 : expression (bv 16)) <- eval (extract v_100 16 32);
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_11)) (concat (mux (sgt v_16 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_16 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_17)) (concat (mux (sgt v_22 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_22 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_23)) (concat (mux (sgt v_28 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_28 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_29)) (concat (mux (sgt v_34 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_34 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_35)) (concat (mux (sgt v_40 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_40 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_41)) (concat (mux (sgt v_46 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_46 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_47)) (concat (mux (sgt v_52 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_52 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_53)) (concat (mux (sgt v_58 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_58 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_59)) (concat (mux (sgt v_64 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_64 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_65)) (concat (mux (sgt v_70 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_70 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_71)) (concat (mux (sgt v_76 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_76 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_77)) (concat (mux (sgt v_82 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_82 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_83)) (concat (mux (sgt v_88 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_88 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_89)) (concat (mux (sgt v_94 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_94 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_95)) (mux (sgt v_100 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_100 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_101)))))))))))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      (v_4 : expression (bv 8)) <- eval (extract v_3 8 16);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 8)) <- eval (extract v_5 8 16);
      (v_7 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_8 : expression (bv 8)) <- eval (extract v_5 0 8);
      v_9 <- eval (add (sext (mul (sext v_4 16) (concat (expression.bv_nat 8 0) v_6)) 32) (sext (mul (sext v_7 16) (concat (expression.bv_nat 8 0) v_8)) 32));
      (v_10 : expression (bv 16)) <- eval (extract v_9 16 32);
      (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_14 : expression (bv 8)) <- eval (extract v_5 16 24);
      v_15 <- eval (add (sext (mul (sext v_11 16) (concat (expression.bv_nat 8 0) v_12)) 32) (sext (mul (sext v_13 16) (concat (expression.bv_nat 8 0) v_14)) 32));
      (v_16 : expression (bv 16)) <- eval (extract v_15 16 32);
      (v_17 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_18 : expression (bv 8)) <- eval (extract v_5 40 48);
      (v_19 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_20 : expression (bv 8)) <- eval (extract v_5 32 40);
      v_21 <- eval (add (sext (mul (sext v_17 16) (concat (expression.bv_nat 8 0) v_18)) 32) (sext (mul (sext v_19 16) (concat (expression.bv_nat 8 0) v_20)) 32));
      (v_22 : expression (bv 16)) <- eval (extract v_21 16 32);
      (v_23 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_24 : expression (bv 8)) <- eval (extract v_5 56 64);
      (v_25 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_26 : expression (bv 8)) <- eval (extract v_5 48 56);
      v_27 <- eval (add (sext (mul (sext v_23 16) (concat (expression.bv_nat 8 0) v_24)) 32) (sext (mul (sext v_25 16) (concat (expression.bv_nat 8 0) v_26)) 32));
      (v_28 : expression (bv 16)) <- eval (extract v_27 16 32);
      (v_29 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_30 : expression (bv 8)) <- eval (extract v_5 72 80);
      (v_31 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_32 : expression (bv 8)) <- eval (extract v_5 64 72);
      v_33 <- eval (add (sext (mul (sext v_29 16) (concat (expression.bv_nat 8 0) v_30)) 32) (sext (mul (sext v_31 16) (concat (expression.bv_nat 8 0) v_32)) 32));
      (v_34 : expression (bv 16)) <- eval (extract v_33 16 32);
      (v_35 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_36 : expression (bv 8)) <- eval (extract v_5 88 96);
      (v_37 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_38 : expression (bv 8)) <- eval (extract v_5 80 88);
      v_39 <- eval (add (sext (mul (sext v_35 16) (concat (expression.bv_nat 8 0) v_36)) 32) (sext (mul (sext v_37 16) (concat (expression.bv_nat 8 0) v_38)) 32));
      (v_40 : expression (bv 16)) <- eval (extract v_39 16 32);
      (v_41 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_42 : expression (bv 8)) <- eval (extract v_5 104 112);
      (v_43 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_44 : expression (bv 8)) <- eval (extract v_5 96 104);
      v_45 <- eval (add (sext (mul (sext v_41 16) (concat (expression.bv_nat 8 0) v_42)) 32) (sext (mul (sext v_43 16) (concat (expression.bv_nat 8 0) v_44)) 32));
      (v_46 : expression (bv 16)) <- eval (extract v_45 16 32);
      (v_47 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_48 : expression (bv 8)) <- eval (extract v_5 120 128);
      (v_49 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_50 : expression (bv 8)) <- eval (extract v_5 112 120);
      v_51 <- eval (add (sext (mul (sext v_47 16) (concat (expression.bv_nat 8 0) v_48)) 32) (sext (mul (sext v_49 16) (concat (expression.bv_nat 8 0) v_50)) 32));
      (v_52 : expression (bv 16)) <- eval (extract v_51 16 32);
      setRegister (lhs.of_reg xmm_2) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_10)) (concat (mux (sgt v_15 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_16)) (concat (mux (sgt v_21 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_21 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_22)) (concat (mux (sgt v_27 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_27 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_28)) (concat (mux (sgt v_33 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_33 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_34)) (concat (mux (sgt v_39 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_39 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_40)) (concat (mux (sgt v_45 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_45 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_46)) (mux (sgt v_51 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_51 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_52)))))))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      (v_4 : expression (bv 8)) <- eval (extract v_3 8 16);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 8)) <- eval (extract v_5 8 16);
      (v_7 : expression (bv 8)) <- eval (extract v_3 0 8);
      (v_8 : expression (bv 8)) <- eval (extract v_5 0 8);
      v_9 <- eval (add (sext (mul (sext v_4 16) (concat (expression.bv_nat 8 0) v_6)) 32) (sext (mul (sext v_7 16) (concat (expression.bv_nat 8 0) v_8)) 32));
      (v_10 : expression (bv 16)) <- eval (extract v_9 16 32);
      (v_11 : expression (bv 8)) <- eval (extract v_3 24 32);
      (v_12 : expression (bv 8)) <- eval (extract v_5 24 32);
      (v_13 : expression (bv 8)) <- eval (extract v_3 16 24);
      (v_14 : expression (bv 8)) <- eval (extract v_5 16 24);
      v_15 <- eval (add (sext (mul (sext v_11 16) (concat (expression.bv_nat 8 0) v_12)) 32) (sext (mul (sext v_13 16) (concat (expression.bv_nat 8 0) v_14)) 32));
      (v_16 : expression (bv 16)) <- eval (extract v_15 16 32);
      (v_17 : expression (bv 8)) <- eval (extract v_3 40 48);
      (v_18 : expression (bv 8)) <- eval (extract v_5 40 48);
      (v_19 : expression (bv 8)) <- eval (extract v_3 32 40);
      (v_20 : expression (bv 8)) <- eval (extract v_5 32 40);
      v_21 <- eval (add (sext (mul (sext v_17 16) (concat (expression.bv_nat 8 0) v_18)) 32) (sext (mul (sext v_19 16) (concat (expression.bv_nat 8 0) v_20)) 32));
      (v_22 : expression (bv 16)) <- eval (extract v_21 16 32);
      (v_23 : expression (bv 8)) <- eval (extract v_3 56 64);
      (v_24 : expression (bv 8)) <- eval (extract v_5 56 64);
      (v_25 : expression (bv 8)) <- eval (extract v_3 48 56);
      (v_26 : expression (bv 8)) <- eval (extract v_5 48 56);
      v_27 <- eval (add (sext (mul (sext v_23 16) (concat (expression.bv_nat 8 0) v_24)) 32) (sext (mul (sext v_25 16) (concat (expression.bv_nat 8 0) v_26)) 32));
      (v_28 : expression (bv 16)) <- eval (extract v_27 16 32);
      (v_29 : expression (bv 8)) <- eval (extract v_3 72 80);
      (v_30 : expression (bv 8)) <- eval (extract v_5 72 80);
      (v_31 : expression (bv 8)) <- eval (extract v_3 64 72);
      (v_32 : expression (bv 8)) <- eval (extract v_5 64 72);
      v_33 <- eval (add (sext (mul (sext v_29 16) (concat (expression.bv_nat 8 0) v_30)) 32) (sext (mul (sext v_31 16) (concat (expression.bv_nat 8 0) v_32)) 32));
      (v_34 : expression (bv 16)) <- eval (extract v_33 16 32);
      (v_35 : expression (bv 8)) <- eval (extract v_3 88 96);
      (v_36 : expression (bv 8)) <- eval (extract v_5 88 96);
      (v_37 : expression (bv 8)) <- eval (extract v_3 80 88);
      (v_38 : expression (bv 8)) <- eval (extract v_5 80 88);
      v_39 <- eval (add (sext (mul (sext v_35 16) (concat (expression.bv_nat 8 0) v_36)) 32) (sext (mul (sext v_37 16) (concat (expression.bv_nat 8 0) v_38)) 32));
      (v_40 : expression (bv 16)) <- eval (extract v_39 16 32);
      (v_41 : expression (bv 8)) <- eval (extract v_3 104 112);
      (v_42 : expression (bv 8)) <- eval (extract v_5 104 112);
      (v_43 : expression (bv 8)) <- eval (extract v_3 96 104);
      (v_44 : expression (bv 8)) <- eval (extract v_5 96 104);
      v_45 <- eval (add (sext (mul (sext v_41 16) (concat (expression.bv_nat 8 0) v_42)) 32) (sext (mul (sext v_43 16) (concat (expression.bv_nat 8 0) v_44)) 32));
      (v_46 : expression (bv 16)) <- eval (extract v_45 16 32);
      (v_47 : expression (bv 8)) <- eval (extract v_3 120 128);
      (v_48 : expression (bv 8)) <- eval (extract v_5 120 128);
      (v_49 : expression (bv 8)) <- eval (extract v_3 112 120);
      (v_50 : expression (bv 8)) <- eval (extract v_5 112 120);
      v_51 <- eval (add (sext (mul (sext v_47 16) (concat (expression.bv_nat 8 0) v_48)) 32) (sext (mul (sext v_49 16) (concat (expression.bv_nat 8 0) v_50)) 32));
      (v_52 : expression (bv 16)) <- eval (extract v_51 16 32);
      (v_53 : expression (bv 8)) <- eval (extract v_3 136 144);
      (v_54 : expression (bv 8)) <- eval (extract v_5 136 144);
      (v_55 : expression (bv 8)) <- eval (extract v_3 128 136);
      (v_56 : expression (bv 8)) <- eval (extract v_5 128 136);
      v_57 <- eval (add (sext (mul (sext v_53 16) (concat (expression.bv_nat 8 0) v_54)) 32) (sext (mul (sext v_55 16) (concat (expression.bv_nat 8 0) v_56)) 32));
      (v_58 : expression (bv 16)) <- eval (extract v_57 16 32);
      (v_59 : expression (bv 8)) <- eval (extract v_3 152 160);
      (v_60 : expression (bv 8)) <- eval (extract v_5 152 160);
      (v_61 : expression (bv 8)) <- eval (extract v_3 144 152);
      (v_62 : expression (bv 8)) <- eval (extract v_5 144 152);
      v_63 <- eval (add (sext (mul (sext v_59 16) (concat (expression.bv_nat 8 0) v_60)) 32) (sext (mul (sext v_61 16) (concat (expression.bv_nat 8 0) v_62)) 32));
      (v_64 : expression (bv 16)) <- eval (extract v_63 16 32);
      (v_65 : expression (bv 8)) <- eval (extract v_3 168 176);
      (v_66 : expression (bv 8)) <- eval (extract v_5 168 176);
      (v_67 : expression (bv 8)) <- eval (extract v_3 160 168);
      (v_68 : expression (bv 8)) <- eval (extract v_5 160 168);
      v_69 <- eval (add (sext (mul (sext v_65 16) (concat (expression.bv_nat 8 0) v_66)) 32) (sext (mul (sext v_67 16) (concat (expression.bv_nat 8 0) v_68)) 32));
      (v_70 : expression (bv 16)) <- eval (extract v_69 16 32);
      (v_71 : expression (bv 8)) <- eval (extract v_3 184 192);
      (v_72 : expression (bv 8)) <- eval (extract v_5 184 192);
      (v_73 : expression (bv 8)) <- eval (extract v_3 176 184);
      (v_74 : expression (bv 8)) <- eval (extract v_5 176 184);
      v_75 <- eval (add (sext (mul (sext v_71 16) (concat (expression.bv_nat 8 0) v_72)) 32) (sext (mul (sext v_73 16) (concat (expression.bv_nat 8 0) v_74)) 32));
      (v_76 : expression (bv 16)) <- eval (extract v_75 16 32);
      (v_77 : expression (bv 8)) <- eval (extract v_3 200 208);
      (v_78 : expression (bv 8)) <- eval (extract v_5 200 208);
      (v_79 : expression (bv 8)) <- eval (extract v_3 192 200);
      (v_80 : expression (bv 8)) <- eval (extract v_5 192 200);
      v_81 <- eval (add (sext (mul (sext v_77 16) (concat (expression.bv_nat 8 0) v_78)) 32) (sext (mul (sext v_79 16) (concat (expression.bv_nat 8 0) v_80)) 32));
      (v_82 : expression (bv 16)) <- eval (extract v_81 16 32);
      (v_83 : expression (bv 8)) <- eval (extract v_3 216 224);
      (v_84 : expression (bv 8)) <- eval (extract v_5 216 224);
      (v_85 : expression (bv 8)) <- eval (extract v_3 208 216);
      (v_86 : expression (bv 8)) <- eval (extract v_5 208 216);
      v_87 <- eval (add (sext (mul (sext v_83 16) (concat (expression.bv_nat 8 0) v_84)) 32) (sext (mul (sext v_85 16) (concat (expression.bv_nat 8 0) v_86)) 32));
      (v_88 : expression (bv 16)) <- eval (extract v_87 16 32);
      (v_89 : expression (bv 8)) <- eval (extract v_3 232 240);
      (v_90 : expression (bv 8)) <- eval (extract v_5 232 240);
      (v_91 : expression (bv 8)) <- eval (extract v_3 224 232);
      (v_92 : expression (bv 8)) <- eval (extract v_5 224 232);
      v_93 <- eval (add (sext (mul (sext v_89 16) (concat (expression.bv_nat 8 0) v_90)) 32) (sext (mul (sext v_91 16) (concat (expression.bv_nat 8 0) v_92)) 32));
      (v_94 : expression (bv 16)) <- eval (extract v_93 16 32);
      (v_95 : expression (bv 8)) <- eval (extract v_3 248 256);
      (v_96 : expression (bv 8)) <- eval (extract v_5 248 256);
      (v_97 : expression (bv 8)) <- eval (extract v_3 240 248);
      (v_98 : expression (bv 8)) <- eval (extract v_5 240 248);
      v_99 <- eval (add (sext (mul (sext v_95 16) (concat (expression.bv_nat 8 0) v_96)) 32) (sext (mul (sext v_97 16) (concat (expression.bv_nat 8 0) v_98)) 32));
      (v_100 : expression (bv 16)) <- eval (extract v_99 16 32);
      setRegister (lhs.of_reg ymm_2) (concat (mux (sgt v_9 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_9 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_10)) (concat (mux (sgt v_15 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_16)) (concat (mux (sgt v_21 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_21 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_22)) (concat (mux (sgt v_27 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_27 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_28)) (concat (mux (sgt v_33 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_33 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_34)) (concat (mux (sgt v_39 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_39 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_40)) (concat (mux (sgt v_45 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_45 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_46)) (concat (mux (sgt v_51 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_51 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_52)) (concat (mux (sgt v_57 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_57 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_58)) (concat (mux (sgt v_63 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_63 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_64)) (concat (mux (sgt v_69 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_69 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_70)) (concat (mux (sgt v_75 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_75 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_76)) (concat (mux (sgt v_81 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_81 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_82)) (concat (mux (sgt v_87 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_87 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_88)) (concat (mux (sgt v_93 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_93 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_94)) (mux (sgt v_99 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_99 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_100)))))))))))))))));
      pure ()
    pat_end
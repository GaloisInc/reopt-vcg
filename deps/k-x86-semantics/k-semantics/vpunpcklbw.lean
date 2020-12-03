def vpunpcklbw : instruction :=
  definst "vpunpcklbw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 16;
      let (v_5 : expression (bv 8)) <- eval (extract v_4 64 72);
      let v_6 <- getRegister (lhs.of_reg xmm_1);
      let (v_7 : expression (bv 8)) <- eval (extract v_6 64 72);
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 8)) <- eval (extract v_4 72 80);
      let (v_10 : expression (bv 8)) <- eval (extract v_6 72 80);
      let v_11 <- eval (concat v_9 v_10);
      let (v_12 : expression (bv 8)) <- eval (extract v_4 80 88);
      let (v_13 : expression (bv 8)) <- eval (extract v_6 80 88);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 8)) <- eval (extract v_4 88 96);
      let (v_16 : expression (bv 8)) <- eval (extract v_6 88 96);
      let v_17 <- eval (concat v_15 v_16);
      let (v_18 : expression (bv 8)) <- eval (extract v_4 96 104);
      let (v_19 : expression (bv 8)) <- eval (extract v_6 96 104);
      let v_20 <- eval (concat v_18 v_19);
      let (v_21 : expression (bv 8)) <- eval (extract v_4 104 112);
      let (v_22 : expression (bv 8)) <- eval (extract v_6 104 112);
      let v_23 <- eval (concat v_21 v_22);
      let (v_24 : expression (bv 8)) <- eval (extract v_4 112 120);
      let (v_25 : expression (bv 8)) <- eval (extract v_6 112 120);
      let v_26 <- eval (concat v_24 v_25);
      let (v_27 : expression (bv 8)) <- eval (extract v_4 120 128);
      let (v_28 : expression (bv 8)) <- eval (extract v_6 120 128);
      let v_29 <- eval (concat v_27 v_28);
      let v_30 <- eval (concat v_26 v_29);
      let v_31 <- eval (concat v_23 v_30);
      let v_32 <- eval (concat v_20 v_31);
      let v_33 <- eval (concat v_17 v_32);
      let v_34 <- eval (concat v_14 v_33);
      let v_35 <- eval (concat v_11 v_34);
      let v_36 <- eval (concat v_8 v_35);
      setRegister (lhs.of_reg xmm_2) v_36;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_0;
      let v_4 <- load v_3 32;
      let (v_5 : expression (bv 8)) <- eval (extract v_4 64 72);
      let v_6 <- getRegister (lhs.of_reg ymm_1);
      let (v_7 : expression (bv 8)) <- eval (extract v_6 64 72);
      let v_8 <- eval (concat v_5 v_7);
      let (v_9 : expression (bv 8)) <- eval (extract v_4 72 80);
      let (v_10 : expression (bv 8)) <- eval (extract v_6 72 80);
      let v_11 <- eval (concat v_9 v_10);
      let (v_12 : expression (bv 8)) <- eval (extract v_4 80 88);
      let (v_13 : expression (bv 8)) <- eval (extract v_6 80 88);
      let v_14 <- eval (concat v_12 v_13);
      let (v_15 : expression (bv 8)) <- eval (extract v_4 88 96);
      let (v_16 : expression (bv 8)) <- eval (extract v_6 88 96);
      let v_17 <- eval (concat v_15 v_16);
      let (v_18 : expression (bv 8)) <- eval (extract v_4 96 104);
      let (v_19 : expression (bv 8)) <- eval (extract v_6 96 104);
      let v_20 <- eval (concat v_18 v_19);
      let (v_21 : expression (bv 8)) <- eval (extract v_4 104 112);
      let (v_22 : expression (bv 8)) <- eval (extract v_6 104 112);
      let v_23 <- eval (concat v_21 v_22);
      let (v_24 : expression (bv 8)) <- eval (extract v_4 112 120);
      let (v_25 : expression (bv 8)) <- eval (extract v_6 112 120);
      let v_26 <- eval (concat v_24 v_25);
      let (v_27 : expression (bv 8)) <- eval (extract v_4 120 128);
      let (v_28 : expression (bv 8)) <- eval (extract v_6 120 128);
      let v_29 <- eval (concat v_27 v_28);
      let (v_30 : expression (bv 8)) <- eval (extract v_4 192 200);
      let (v_31 : expression (bv 8)) <- eval (extract v_6 192 200);
      let v_32 <- eval (concat v_30 v_31);
      let (v_33 : expression (bv 8)) <- eval (extract v_4 200 208);
      let (v_34 : expression (bv 8)) <- eval (extract v_6 200 208);
      let v_35 <- eval (concat v_33 v_34);
      let (v_36 : expression (bv 8)) <- eval (extract v_4 208 216);
      let (v_37 : expression (bv 8)) <- eval (extract v_6 208 216);
      let v_38 <- eval (concat v_36 v_37);
      let (v_39 : expression (bv 8)) <- eval (extract v_4 216 224);
      let (v_40 : expression (bv 8)) <- eval (extract v_6 216 224);
      let v_41 <- eval (concat v_39 v_40);
      let (v_42 : expression (bv 8)) <- eval (extract v_4 224 232);
      let (v_43 : expression (bv 8)) <- eval (extract v_6 224 232);
      let v_44 <- eval (concat v_42 v_43);
      let (v_45 : expression (bv 8)) <- eval (extract v_4 232 240);
      let (v_46 : expression (bv 8)) <- eval (extract v_6 232 240);
      let v_47 <- eval (concat v_45 v_46);
      let (v_48 : expression (bv 8)) <- eval (extract v_4 240 248);
      let (v_49 : expression (bv 8)) <- eval (extract v_6 240 248);
      let v_50 <- eval (concat v_48 v_49);
      let (v_51 : expression (bv 8)) <- eval (extract v_4 248 256);
      let (v_52 : expression (bv 8)) <- eval (extract v_6 248 256);
      let v_53 <- eval (concat v_51 v_52);
      let v_54 <- eval (concat v_50 v_53);
      let v_55 <- eval (concat v_47 v_54);
      let v_56 <- eval (concat v_44 v_55);
      let v_57 <- eval (concat v_41 v_56);
      let v_58 <- eval (concat v_38 v_57);
      let v_59 <- eval (concat v_35 v_58);
      let v_60 <- eval (concat v_32 v_59);
      let v_61 <- eval (concat v_29 v_60);
      let v_62 <- eval (concat v_26 v_61);
      let v_63 <- eval (concat v_23 v_62);
      let v_64 <- eval (concat v_20 v_63);
      let v_65 <- eval (concat v_17 v_64);
      let v_66 <- eval (concat v_14 v_65);
      let v_67 <- eval (concat v_11 v_66);
      let v_68 <- eval (concat v_8 v_67);
      setRegister (lhs.of_reg ymm_2) v_68;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_0);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 64 72);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 64 72);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_9 : expression (bv 8)) <- eval (extract v_5 72 80);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_12 : expression (bv 8)) <- eval (extract v_5 80 88);
      let v_13 <- eval (concat v_11 v_12);
      let (v_14 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_15 : expression (bv 8)) <- eval (extract v_5 88 96);
      let v_16 <- eval (concat v_14 v_15);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_18 : expression (bv 8)) <- eval (extract v_5 96 104);
      let v_19 <- eval (concat v_17 v_18);
      let (v_20 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_21 : expression (bv 8)) <- eval (extract v_5 104 112);
      let v_22 <- eval (concat v_20 v_21);
      let (v_23 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_24 : expression (bv 8)) <- eval (extract v_5 112 120);
      let v_25 <- eval (concat v_23 v_24);
      let (v_26 : expression (bv 8)) <- eval (extract v_3 120 128);
      let (v_27 : expression (bv 8)) <- eval (extract v_5 120 128);
      let v_28 <- eval (concat v_26 v_27);
      let v_29 <- eval (concat v_25 v_28);
      let v_30 <- eval (concat v_22 v_29);
      let v_31 <- eval (concat v_19 v_30);
      let v_32 <- eval (concat v_16 v_31);
      let v_33 <- eval (concat v_13 v_32);
      let v_34 <- eval (concat v_10 v_33);
      let v_35 <- eval (concat v_7 v_34);
      setRegister (lhs.of_reg xmm_2) v_35;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_0);
      let (v_4 : expression (bv 8)) <- eval (extract v_3 64 72);
      let v_5 <- getRegister (lhs.of_reg ymm_1);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 64 72);
      let v_7 <- eval (concat v_4 v_6);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_9 : expression (bv 8)) <- eval (extract v_5 72 80);
      let v_10 <- eval (concat v_8 v_9);
      let (v_11 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_12 : expression (bv 8)) <- eval (extract v_5 80 88);
      let v_13 <- eval (concat v_11 v_12);
      let (v_14 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_15 : expression (bv 8)) <- eval (extract v_5 88 96);
      let v_16 <- eval (concat v_14 v_15);
      let (v_17 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_18 : expression (bv 8)) <- eval (extract v_5 96 104);
      let v_19 <- eval (concat v_17 v_18);
      let (v_20 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_21 : expression (bv 8)) <- eval (extract v_5 104 112);
      let v_22 <- eval (concat v_20 v_21);
      let (v_23 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_24 : expression (bv 8)) <- eval (extract v_5 112 120);
      let v_25 <- eval (concat v_23 v_24);
      let (v_26 : expression (bv 8)) <- eval (extract v_3 120 128);
      let (v_27 : expression (bv 8)) <- eval (extract v_5 120 128);
      let v_28 <- eval (concat v_26 v_27);
      let (v_29 : expression (bv 8)) <- eval (extract v_3 192 200);
      let (v_30 : expression (bv 8)) <- eval (extract v_5 192 200);
      let v_31 <- eval (concat v_29 v_30);
      let (v_32 : expression (bv 8)) <- eval (extract v_3 200 208);
      let (v_33 : expression (bv 8)) <- eval (extract v_5 200 208);
      let v_34 <- eval (concat v_32 v_33);
      let (v_35 : expression (bv 8)) <- eval (extract v_3 208 216);
      let (v_36 : expression (bv 8)) <- eval (extract v_5 208 216);
      let v_37 <- eval (concat v_35 v_36);
      let (v_38 : expression (bv 8)) <- eval (extract v_3 216 224);
      let (v_39 : expression (bv 8)) <- eval (extract v_5 216 224);
      let v_40 <- eval (concat v_38 v_39);
      let (v_41 : expression (bv 8)) <- eval (extract v_3 224 232);
      let (v_42 : expression (bv 8)) <- eval (extract v_5 224 232);
      let v_43 <- eval (concat v_41 v_42);
      let (v_44 : expression (bv 8)) <- eval (extract v_3 232 240);
      let (v_45 : expression (bv 8)) <- eval (extract v_5 232 240);
      let v_46 <- eval (concat v_44 v_45);
      let (v_47 : expression (bv 8)) <- eval (extract v_3 240 248);
      let (v_48 : expression (bv 8)) <- eval (extract v_5 240 248);
      let v_49 <- eval (concat v_47 v_48);
      let (v_50 : expression (bv 8)) <- eval (extract v_3 248 256);
      let (v_51 : expression (bv 8)) <- eval (extract v_5 248 256);
      let v_52 <- eval (concat v_50 v_51);
      let v_53 <- eval (concat v_49 v_52);
      let v_54 <- eval (concat v_46 v_53);
      let v_55 <- eval (concat v_43 v_54);
      let v_56 <- eval (concat v_40 v_55);
      let v_57 <- eval (concat v_37 v_56);
      let v_58 <- eval (concat v_34 v_57);
      let v_59 <- eval (concat v_31 v_58);
      let v_60 <- eval (concat v_28 v_59);
      let v_61 <- eval (concat v_25 v_60);
      let v_62 <- eval (concat v_22 v_61);
      let v_63 <- eval (concat v_19 v_62);
      let v_64 <- eval (concat v_16 v_63);
      let v_65 <- eval (concat v_13 v_64);
      let v_66 <- eval (concat v_10 v_65);
      let v_67 <- eval (concat v_7 v_66);
      setRegister (lhs.of_reg ymm_2) v_67;
      pure ()
     action

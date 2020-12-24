def vpsubsw : instruction :=
  definst "vpsubsw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let v_8 <- eval (sub (sext v_4 18) (sext v_7 18));
      let (v_9 : expression (bv 16)) <- eval (extract v_8 2 18);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_11 : expression (bv 16)) <- eval (extract v_6 16 32);
      let v_12 <- eval (sub (sext v_10 18) (sext v_11 18));
      let (v_13 : expression (bv 16)) <- eval (extract v_12 2 18);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_15 : expression (bv 16)) <- eval (extract v_6 32 48);
      let v_16 <- eval (sub (sext v_14 18) (sext v_15 18));
      let (v_17 : expression (bv 16)) <- eval (extract v_16 2 18);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 48 64);
      let v_20 <- eval (sub (sext v_18 18) (sext v_19 18));
      let (v_21 : expression (bv 16)) <- eval (extract v_20 2 18);
      let (v_22 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_23 : expression (bv 16)) <- eval (extract v_6 64 80);
      let v_24 <- eval (sub (sext v_22 18) (sext v_23 18));
      let (v_25 : expression (bv 16)) <- eval (extract v_24 2 18);
      let (v_26 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_27 : expression (bv 16)) <- eval (extract v_6 80 96);
      let v_28 <- eval (sub (sext v_26 18) (sext v_27 18));
      let (v_29 : expression (bv 16)) <- eval (extract v_28 2 18);
      let (v_30 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_31 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_32 <- eval (sub (sext v_30 18) (sext v_31 18));
      let (v_33 : expression (bv 16)) <- eval (extract v_32 2 18);
      let (v_34 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_35 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_36 <- eval (sub (sext v_34 18) (sext v_35 18));
      let (v_37 : expression (bv 16)) <- eval (extract v_36 2 18);
      let v_38 <- eval (concat (mux (sgt v_32 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_32 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_33)) (mux (sgt v_36 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_36 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_37)));
      let v_39 <- eval (concat (mux (sgt v_28 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_28 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_29)) v_38);
      let v_40 <- eval (concat (mux (sgt v_24 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_24 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_25)) v_39);
      let v_41 <- eval (concat (mux (sgt v_20 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_20 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_21)) v_40);
      let v_42 <- eval (concat (mux (sgt v_16 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_16 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_17)) v_41);
      let v_43 <- eval (concat (mux (sgt v_12 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_13)) v_42);
      let v_44 <- eval (concat (mux (sgt v_8 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_9)) v_43);
      setRegister (lhs.of_reg xmm_2) v_44;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 32;
      let (v_7 : expression (bv 16)) <- eval (extract v_6 0 16);
      let v_8 <- eval (sub (sext v_4 18) (sext v_7 18));
      let (v_9 : expression (bv 16)) <- eval (extract v_8 2 18);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_11 : expression (bv 16)) <- eval (extract v_6 16 32);
      let v_12 <- eval (sub (sext v_10 18) (sext v_11 18));
      let (v_13 : expression (bv 16)) <- eval (extract v_12 2 18);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_15 : expression (bv 16)) <- eval (extract v_6 32 48);
      let v_16 <- eval (sub (sext v_14 18) (sext v_15 18));
      let (v_17 : expression (bv 16)) <- eval (extract v_16 2 18);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_19 : expression (bv 16)) <- eval (extract v_6 48 64);
      let v_20 <- eval (sub (sext v_18 18) (sext v_19 18));
      let (v_21 : expression (bv 16)) <- eval (extract v_20 2 18);
      let (v_22 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_23 : expression (bv 16)) <- eval (extract v_6 64 80);
      let v_24 <- eval (sub (sext v_22 18) (sext v_23 18));
      let (v_25 : expression (bv 16)) <- eval (extract v_24 2 18);
      let (v_26 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_27 : expression (bv 16)) <- eval (extract v_6 80 96);
      let v_28 <- eval (sub (sext v_26 18) (sext v_27 18));
      let (v_29 : expression (bv 16)) <- eval (extract v_28 2 18);
      let (v_30 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_31 : expression (bv 16)) <- eval (extract v_6 96 112);
      let v_32 <- eval (sub (sext v_30 18) (sext v_31 18));
      let (v_33 : expression (bv 16)) <- eval (extract v_32 2 18);
      let (v_34 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_35 : expression (bv 16)) <- eval (extract v_6 112 128);
      let v_36 <- eval (sub (sext v_34 18) (sext v_35 18));
      let (v_37 : expression (bv 16)) <- eval (extract v_36 2 18);
      let (v_38 : expression (bv 16)) <- eval (extract v_3 128 144);
      let (v_39 : expression (bv 16)) <- eval (extract v_6 128 144);
      let v_40 <- eval (sub (sext v_38 18) (sext v_39 18));
      let (v_41 : expression (bv 16)) <- eval (extract v_40 2 18);
      let (v_42 : expression (bv 16)) <- eval (extract v_3 144 160);
      let (v_43 : expression (bv 16)) <- eval (extract v_6 144 160);
      let v_44 <- eval (sub (sext v_42 18) (sext v_43 18));
      let (v_45 : expression (bv 16)) <- eval (extract v_44 2 18);
      let (v_46 : expression (bv 16)) <- eval (extract v_3 160 176);
      let (v_47 : expression (bv 16)) <- eval (extract v_6 160 176);
      let v_48 <- eval (sub (sext v_46 18) (sext v_47 18));
      let (v_49 : expression (bv 16)) <- eval (extract v_48 2 18);
      let (v_50 : expression (bv 16)) <- eval (extract v_3 176 192);
      let (v_51 : expression (bv 16)) <- eval (extract v_6 176 192);
      let v_52 <- eval (sub (sext v_50 18) (sext v_51 18));
      let (v_53 : expression (bv 16)) <- eval (extract v_52 2 18);
      let (v_54 : expression (bv 16)) <- eval (extract v_3 192 208);
      let (v_55 : expression (bv 16)) <- eval (extract v_6 192 208);
      let v_56 <- eval (sub (sext v_54 18) (sext v_55 18));
      let (v_57 : expression (bv 16)) <- eval (extract v_56 2 18);
      let (v_58 : expression (bv 16)) <- eval (extract v_3 208 224);
      let (v_59 : expression (bv 16)) <- eval (extract v_6 208 224);
      let v_60 <- eval (sub (sext v_58 18) (sext v_59 18));
      let (v_61 : expression (bv 16)) <- eval (extract v_60 2 18);
      let (v_62 : expression (bv 16)) <- eval (extract v_3 224 240);
      let (v_63 : expression (bv 16)) <- eval (extract v_6 224 240);
      let v_64 <- eval (sub (sext v_62 18) (sext v_63 18));
      let (v_65 : expression (bv 16)) <- eval (extract v_64 2 18);
      let (v_66 : expression (bv 16)) <- eval (extract v_3 240 256);
      let (v_67 : expression (bv 16)) <- eval (extract v_6 240 256);
      let v_68 <- eval (sub (sext v_66 18) (sext v_67 18));
      let (v_69 : expression (bv 16)) <- eval (extract v_68 2 18);
      let v_70 <- eval (concat (mux (sgt v_64 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_64 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_65)) (mux (sgt v_68 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_68 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_69)));
      let v_71 <- eval (concat (mux (sgt v_60 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_60 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_61)) v_70);
      let v_72 <- eval (concat (mux (sgt v_56 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_56 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_57)) v_71);
      let v_73 <- eval (concat (mux (sgt v_52 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_52 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_53)) v_72);
      let v_74 <- eval (concat (mux (sgt v_48 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_48 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_49)) v_73);
      let v_75 <- eval (concat (mux (sgt v_44 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_44 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_45)) v_74);
      let v_76 <- eval (concat (mux (sgt v_40 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_40 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_41)) v_75);
      let v_77 <- eval (concat (mux (sgt v_36 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_36 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_37)) v_76);
      let v_78 <- eval (concat (mux (sgt v_32 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_32 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_33)) v_77);
      let v_79 <- eval (concat (mux (sgt v_28 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_28 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_29)) v_78);
      let v_80 <- eval (concat (mux (sgt v_24 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_24 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_25)) v_79);
      let v_81 <- eval (concat (mux (sgt v_20 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_20 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_21)) v_80);
      let v_82 <- eval (concat (mux (sgt v_16 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_16 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_17)) v_81);
      let v_83 <- eval (concat (mux (sgt v_12 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_12 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_13)) v_82);
      let v_84 <- eval (concat (mux (sgt v_8 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_8 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_9)) v_83);
      setRegister (lhs.of_reg ymm_2) v_84;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_7 <- eval (sub (sext v_4 18) (sext v_6 18));
      let (v_8 : expression (bv 16)) <- eval (extract v_7 2 18);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 16 32);
      let v_11 <- eval (sub (sext v_9 18) (sext v_10 18));
      let (v_12 : expression (bv 16)) <- eval (extract v_11 2 18);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 32 48);
      let v_15 <- eval (sub (sext v_13 18) (sext v_14 18));
      let (v_16 : expression (bv 16)) <- eval (extract v_15 2 18);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 48 64);
      let v_19 <- eval (sub (sext v_17 18) (sext v_18 18));
      let (v_20 : expression (bv 16)) <- eval (extract v_19 2 18);
      let (v_21 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_22 : expression (bv 16)) <- eval (extract v_5 64 80);
      let v_23 <- eval (sub (sext v_21 18) (sext v_22 18));
      let (v_24 : expression (bv 16)) <- eval (extract v_23 2 18);
      let (v_25 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_26 : expression (bv 16)) <- eval (extract v_5 80 96);
      let v_27 <- eval (sub (sext v_25 18) (sext v_26 18));
      let (v_28 : expression (bv 16)) <- eval (extract v_27 2 18);
      let (v_29 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_30 : expression (bv 16)) <- eval (extract v_5 96 112);
      let v_31 <- eval (sub (sext v_29 18) (sext v_30 18));
      let (v_32 : expression (bv 16)) <- eval (extract v_31 2 18);
      let (v_33 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_34 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_35 <- eval (sub (sext v_33 18) (sext v_34 18));
      let (v_36 : expression (bv 16)) <- eval (extract v_35 2 18);
      let v_37 <- eval (concat (mux (sgt v_31 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_31 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_32)) (mux (sgt v_35 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_35 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_36)));
      let v_38 <- eval (concat (mux (sgt v_27 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_27 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_28)) v_37);
      let v_39 <- eval (concat (mux (sgt v_23 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_23 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_24)) v_38);
      let v_40 <- eval (concat (mux (sgt v_19 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_19 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_20)) v_39);
      let v_41 <- eval (concat (mux (sgt v_15 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_16)) v_40);
      let v_42 <- eval (concat (mux (sgt v_11 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_12)) v_41);
      let v_43 <- eval (concat (mux (sgt v_7 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_8)) v_42);
      setRegister (lhs.of_reg xmm_2) v_43;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- getRegister (lhs.of_reg ymm_0);
      let (v_6 : expression (bv 16)) <- eval (extract v_5 0 16);
      let v_7 <- eval (sub (sext v_4 18) (sext v_6 18));
      let (v_8 : expression (bv 16)) <- eval (extract v_7 2 18);
      let (v_9 : expression (bv 16)) <- eval (extract v_3 16 32);
      let (v_10 : expression (bv 16)) <- eval (extract v_5 16 32);
      let v_11 <- eval (sub (sext v_9 18) (sext v_10 18));
      let (v_12 : expression (bv 16)) <- eval (extract v_11 2 18);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 32 48);
      let (v_14 : expression (bv 16)) <- eval (extract v_5 32 48);
      let v_15 <- eval (sub (sext v_13 18) (sext v_14 18));
      let (v_16 : expression (bv 16)) <- eval (extract v_15 2 18);
      let (v_17 : expression (bv 16)) <- eval (extract v_3 48 64);
      let (v_18 : expression (bv 16)) <- eval (extract v_5 48 64);
      let v_19 <- eval (sub (sext v_17 18) (sext v_18 18));
      let (v_20 : expression (bv 16)) <- eval (extract v_19 2 18);
      let (v_21 : expression (bv 16)) <- eval (extract v_3 64 80);
      let (v_22 : expression (bv 16)) <- eval (extract v_5 64 80);
      let v_23 <- eval (sub (sext v_21 18) (sext v_22 18));
      let (v_24 : expression (bv 16)) <- eval (extract v_23 2 18);
      let (v_25 : expression (bv 16)) <- eval (extract v_3 80 96);
      let (v_26 : expression (bv 16)) <- eval (extract v_5 80 96);
      let v_27 <- eval (sub (sext v_25 18) (sext v_26 18));
      let (v_28 : expression (bv 16)) <- eval (extract v_27 2 18);
      let (v_29 : expression (bv 16)) <- eval (extract v_3 96 112);
      let (v_30 : expression (bv 16)) <- eval (extract v_5 96 112);
      let v_31 <- eval (sub (sext v_29 18) (sext v_30 18));
      let (v_32 : expression (bv 16)) <- eval (extract v_31 2 18);
      let (v_33 : expression (bv 16)) <- eval (extract v_3 112 128);
      let (v_34 : expression (bv 16)) <- eval (extract v_5 112 128);
      let v_35 <- eval (sub (sext v_33 18) (sext v_34 18));
      let (v_36 : expression (bv 16)) <- eval (extract v_35 2 18);
      let (v_37 : expression (bv 16)) <- eval (extract v_3 128 144);
      let (v_38 : expression (bv 16)) <- eval (extract v_5 128 144);
      let v_39 <- eval (sub (sext v_37 18) (sext v_38 18));
      let (v_40 : expression (bv 16)) <- eval (extract v_39 2 18);
      let (v_41 : expression (bv 16)) <- eval (extract v_3 144 160);
      let (v_42 : expression (bv 16)) <- eval (extract v_5 144 160);
      let v_43 <- eval (sub (sext v_41 18) (sext v_42 18));
      let (v_44 : expression (bv 16)) <- eval (extract v_43 2 18);
      let (v_45 : expression (bv 16)) <- eval (extract v_3 160 176);
      let (v_46 : expression (bv 16)) <- eval (extract v_5 160 176);
      let v_47 <- eval (sub (sext v_45 18) (sext v_46 18));
      let (v_48 : expression (bv 16)) <- eval (extract v_47 2 18);
      let (v_49 : expression (bv 16)) <- eval (extract v_3 176 192);
      let (v_50 : expression (bv 16)) <- eval (extract v_5 176 192);
      let v_51 <- eval (sub (sext v_49 18) (sext v_50 18));
      let (v_52 : expression (bv 16)) <- eval (extract v_51 2 18);
      let (v_53 : expression (bv 16)) <- eval (extract v_3 192 208);
      let (v_54 : expression (bv 16)) <- eval (extract v_5 192 208);
      let v_55 <- eval (sub (sext v_53 18) (sext v_54 18));
      let (v_56 : expression (bv 16)) <- eval (extract v_55 2 18);
      let (v_57 : expression (bv 16)) <- eval (extract v_3 208 224);
      let (v_58 : expression (bv 16)) <- eval (extract v_5 208 224);
      let v_59 <- eval (sub (sext v_57 18) (sext v_58 18));
      let (v_60 : expression (bv 16)) <- eval (extract v_59 2 18);
      let (v_61 : expression (bv 16)) <- eval (extract v_3 224 240);
      let (v_62 : expression (bv 16)) <- eval (extract v_5 224 240);
      let v_63 <- eval (sub (sext v_61 18) (sext v_62 18));
      let (v_64 : expression (bv 16)) <- eval (extract v_63 2 18);
      let (v_65 : expression (bv 16)) <- eval (extract v_3 240 256);
      let (v_66 : expression (bv 16)) <- eval (extract v_5 240 256);
      let v_67 <- eval (sub (sext v_65 18) (sext v_66 18));
      let (v_68 : expression (bv 16)) <- eval (extract v_67 2 18);
      let v_69 <- eval (concat (mux (sgt v_63 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_63 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_64)) (mux (sgt v_67 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_67 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_68)));
      let v_70 <- eval (concat (mux (sgt v_59 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_59 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_60)) v_69);
      let v_71 <- eval (concat (mux (sgt v_55 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_55 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_56)) v_70);
      let v_72 <- eval (concat (mux (sgt v_51 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_51 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_52)) v_71);
      let v_73 <- eval (concat (mux (sgt v_47 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_47 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_48)) v_72);
      let v_74 <- eval (concat (mux (sgt v_43 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_43 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_44)) v_73);
      let v_75 <- eval (concat (mux (sgt v_39 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_39 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_40)) v_74);
      let v_76 <- eval (concat (mux (sgt v_35 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_35 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_36)) v_75);
      let v_77 <- eval (concat (mux (sgt v_31 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_31 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_32)) v_76);
      let v_78 <- eval (concat (mux (sgt v_27 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_27 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_28)) v_77);
      let v_79 <- eval (concat (mux (sgt v_23 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_23 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_24)) v_78);
      let v_80 <- eval (concat (mux (sgt v_19 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_19 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_20)) v_79);
      let v_81 <- eval (concat (mux (sgt v_15 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_15 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_16)) v_80);
      let v_82 <- eval (concat (mux (sgt v_11 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_12)) v_81);
      let v_83 <- eval (concat (mux (sgt v_7 (expression.bv_nat 18 32767)) (expression.bv_nat 16 32767) (mux (slt v_7 (expression.bv_nat 18 229376)) (expression.bv_nat 16 32768) v_8)) v_82);
      setRegister (lhs.of_reg ymm_2) v_83;
      pure ()
     action
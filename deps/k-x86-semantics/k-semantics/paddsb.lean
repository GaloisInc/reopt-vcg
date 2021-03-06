def paddsb : instruction :=
  definst "paddsb" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      let v_4 <- evaluateAddress mem_0;
      let v_5 <- load v_4 16;
      let (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      let v_7 <- eval (add (sext v_3 16) (sext v_6 16));
      let (v_8 : expression (bv 8)) <- eval (extract v_7 8 16);
      let (v_9 : expression (bv 8)) <- eval (extract v_2 8 16);
      let (v_10 : expression (bv 8)) <- eval (extract v_5 8 16);
      let v_11 <- eval (add (sext v_9 16) (sext v_10 16));
      let (v_12 : expression (bv 8)) <- eval (extract v_11 8 16);
      let (v_13 : expression (bv 8)) <- eval (extract v_2 16 24);
      let (v_14 : expression (bv 8)) <- eval (extract v_5 16 24);
      let v_15 <- eval (add (sext v_13 16) (sext v_14 16));
      let (v_16 : expression (bv 8)) <- eval (extract v_15 8 16);
      let (v_17 : expression (bv 8)) <- eval (extract v_2 24 32);
      let (v_18 : expression (bv 8)) <- eval (extract v_5 24 32);
      let v_19 <- eval (add (sext v_17 16) (sext v_18 16));
      let (v_20 : expression (bv 8)) <- eval (extract v_19 8 16);
      let (v_21 : expression (bv 8)) <- eval (extract v_2 32 40);
      let (v_22 : expression (bv 8)) <- eval (extract v_5 32 40);
      let v_23 <- eval (add (sext v_21 16) (sext v_22 16));
      let (v_24 : expression (bv 8)) <- eval (extract v_23 8 16);
      let (v_25 : expression (bv 8)) <- eval (extract v_2 40 48);
      let (v_26 : expression (bv 8)) <- eval (extract v_5 40 48);
      let v_27 <- eval (add (sext v_25 16) (sext v_26 16));
      let (v_28 : expression (bv 8)) <- eval (extract v_27 8 16);
      let (v_29 : expression (bv 8)) <- eval (extract v_2 48 56);
      let (v_30 : expression (bv 8)) <- eval (extract v_5 48 56);
      let v_31 <- eval (add (sext v_29 16) (sext v_30 16));
      let (v_32 : expression (bv 8)) <- eval (extract v_31 8 16);
      let (v_33 : expression (bv 8)) <- eval (extract v_2 56 64);
      let (v_34 : expression (bv 8)) <- eval (extract v_5 56 64);
      let v_35 <- eval (add (sext v_33 16) (sext v_34 16));
      let (v_36 : expression (bv 8)) <- eval (extract v_35 8 16);
      let (v_37 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_38 : expression (bv 8)) <- eval (extract v_5 64 72);
      let v_39 <- eval (add (sext v_37 16) (sext v_38 16));
      let (v_40 : expression (bv 8)) <- eval (extract v_39 8 16);
      let (v_41 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_42 : expression (bv 8)) <- eval (extract v_5 72 80);
      let v_43 <- eval (add (sext v_41 16) (sext v_42 16));
      let (v_44 : expression (bv 8)) <- eval (extract v_43 8 16);
      let (v_45 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_46 : expression (bv 8)) <- eval (extract v_5 80 88);
      let v_47 <- eval (add (sext v_45 16) (sext v_46 16));
      let (v_48 : expression (bv 8)) <- eval (extract v_47 8 16);
      let (v_49 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_50 : expression (bv 8)) <- eval (extract v_5 88 96);
      let v_51 <- eval (add (sext v_49 16) (sext v_50 16));
      let (v_52 : expression (bv 8)) <- eval (extract v_51 8 16);
      let (v_53 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_54 : expression (bv 8)) <- eval (extract v_5 96 104);
      let v_55 <- eval (add (sext v_53 16) (sext v_54 16));
      let (v_56 : expression (bv 8)) <- eval (extract v_55 8 16);
      let (v_57 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_58 : expression (bv 8)) <- eval (extract v_5 104 112);
      let v_59 <- eval (add (sext v_57 16) (sext v_58 16));
      let (v_60 : expression (bv 8)) <- eval (extract v_59 8 16);
      let (v_61 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_62 : expression (bv 8)) <- eval (extract v_5 112 120);
      let v_63 <- eval (add (sext v_61 16) (sext v_62 16));
      let (v_64 : expression (bv 8)) <- eval (extract v_63 8 16);
      let (v_65 : expression (bv 8)) <- eval (extract v_2 120 128);
      let (v_66 : expression (bv 8)) <- eval (extract v_5 120 128);
      let v_67 <- eval (add (sext v_65 16) (sext v_66 16));
      let (v_68 : expression (bv 8)) <- eval (extract v_67 8 16);
      let v_69 <- eval (concat (mux (sgt v_63 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_63 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_64)) (mux (sgt v_67 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_67 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_68)));
      let v_70 <- eval (concat (mux (sgt v_59 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_59 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_60)) v_69);
      let v_71 <- eval (concat (mux (sgt v_55 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_55 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_56)) v_70);
      let v_72 <- eval (concat (mux (sgt v_51 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_51 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_52)) v_71);
      let v_73 <- eval (concat (mux (sgt v_47 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_47 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_48)) v_72);
      let v_74 <- eval (concat (mux (sgt v_43 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_43 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_44)) v_73);
      let v_75 <- eval (concat (mux (sgt v_39 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_39 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_40)) v_74);
      let v_76 <- eval (concat (mux (sgt v_35 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_35 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_36)) v_75);
      let v_77 <- eval (concat (mux (sgt v_31 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_31 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_32)) v_76);
      let v_78 <- eval (concat (mux (sgt v_27 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_27 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_28)) v_77);
      let v_79 <- eval (concat (mux (sgt v_23 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_23 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_24)) v_78);
      let v_80 <- eval (concat (mux (sgt v_19 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_19 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_20)) v_79);
      let v_81 <- eval (concat (mux (sgt v_15 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_15 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_16)) v_80);
      let v_82 <- eval (concat (mux (sgt v_11 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_11 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_12)) v_81);
      let v_83 <- eval (concat (mux (sgt v_7 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_7 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_8)) v_82);
      setRegister (lhs.of_reg xmm_1) v_83;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 0 8);
      let v_4 <- getRegister (lhs.of_reg xmm_0);
      let (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      let v_6 <- eval (add (sext v_3 16) (sext v_5 16));
      let (v_7 : expression (bv 8)) <- eval (extract v_6 8 16);
      let (v_8 : expression (bv 8)) <- eval (extract v_2 8 16);
      let (v_9 : expression (bv 8)) <- eval (extract v_4 8 16);
      let v_10 <- eval (add (sext v_8 16) (sext v_9 16));
      let (v_11 : expression (bv 8)) <- eval (extract v_10 8 16);
      let (v_12 : expression (bv 8)) <- eval (extract v_2 16 24);
      let (v_13 : expression (bv 8)) <- eval (extract v_4 16 24);
      let v_14 <- eval (add (sext v_12 16) (sext v_13 16));
      let (v_15 : expression (bv 8)) <- eval (extract v_14 8 16);
      let (v_16 : expression (bv 8)) <- eval (extract v_2 24 32);
      let (v_17 : expression (bv 8)) <- eval (extract v_4 24 32);
      let v_18 <- eval (add (sext v_16 16) (sext v_17 16));
      let (v_19 : expression (bv 8)) <- eval (extract v_18 8 16);
      let (v_20 : expression (bv 8)) <- eval (extract v_2 32 40);
      let (v_21 : expression (bv 8)) <- eval (extract v_4 32 40);
      let v_22 <- eval (add (sext v_20 16) (sext v_21 16));
      let (v_23 : expression (bv 8)) <- eval (extract v_22 8 16);
      let (v_24 : expression (bv 8)) <- eval (extract v_2 40 48);
      let (v_25 : expression (bv 8)) <- eval (extract v_4 40 48);
      let v_26 <- eval (add (sext v_24 16) (sext v_25 16));
      let (v_27 : expression (bv 8)) <- eval (extract v_26 8 16);
      let (v_28 : expression (bv 8)) <- eval (extract v_2 48 56);
      let (v_29 : expression (bv 8)) <- eval (extract v_4 48 56);
      let v_30 <- eval (add (sext v_28 16) (sext v_29 16));
      let (v_31 : expression (bv 8)) <- eval (extract v_30 8 16);
      let (v_32 : expression (bv 8)) <- eval (extract v_2 56 64);
      let (v_33 : expression (bv 8)) <- eval (extract v_4 56 64);
      let v_34 <- eval (add (sext v_32 16) (sext v_33 16));
      let (v_35 : expression (bv 8)) <- eval (extract v_34 8 16);
      let (v_36 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_37 : expression (bv 8)) <- eval (extract v_4 64 72);
      let v_38 <- eval (add (sext v_36 16) (sext v_37 16));
      let (v_39 : expression (bv 8)) <- eval (extract v_38 8 16);
      let (v_40 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_41 : expression (bv 8)) <- eval (extract v_4 72 80);
      let v_42 <- eval (add (sext v_40 16) (sext v_41 16));
      let (v_43 : expression (bv 8)) <- eval (extract v_42 8 16);
      let (v_44 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_45 : expression (bv 8)) <- eval (extract v_4 80 88);
      let v_46 <- eval (add (sext v_44 16) (sext v_45 16));
      let (v_47 : expression (bv 8)) <- eval (extract v_46 8 16);
      let (v_48 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_49 : expression (bv 8)) <- eval (extract v_4 88 96);
      let v_50 <- eval (add (sext v_48 16) (sext v_49 16));
      let (v_51 : expression (bv 8)) <- eval (extract v_50 8 16);
      let (v_52 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_53 : expression (bv 8)) <- eval (extract v_4 96 104);
      let v_54 <- eval (add (sext v_52 16) (sext v_53 16));
      let (v_55 : expression (bv 8)) <- eval (extract v_54 8 16);
      let (v_56 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_57 : expression (bv 8)) <- eval (extract v_4 104 112);
      let v_58 <- eval (add (sext v_56 16) (sext v_57 16));
      let (v_59 : expression (bv 8)) <- eval (extract v_58 8 16);
      let (v_60 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_61 : expression (bv 8)) <- eval (extract v_4 112 120);
      let v_62 <- eval (add (sext v_60 16) (sext v_61 16));
      let (v_63 : expression (bv 8)) <- eval (extract v_62 8 16);
      let (v_64 : expression (bv 8)) <- eval (extract v_2 120 128);
      let (v_65 : expression (bv 8)) <- eval (extract v_4 120 128);
      let v_66 <- eval (add (sext v_64 16) (sext v_65 16));
      let (v_67 : expression (bv 8)) <- eval (extract v_66 8 16);
      let v_68 <- eval (concat (mux (sgt v_62 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_62 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_63)) (mux (sgt v_66 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_66 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_67)));
      let v_69 <- eval (concat (mux (sgt v_58 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_58 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_59)) v_68);
      let v_70 <- eval (concat (mux (sgt v_54 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_54 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_55)) v_69);
      let v_71 <- eval (concat (mux (sgt v_50 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_50 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_51)) v_70);
      let v_72 <- eval (concat (mux (sgt v_46 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_46 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_47)) v_71);
      let v_73 <- eval (concat (mux (sgt v_42 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_42 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_43)) v_72);
      let v_74 <- eval (concat (mux (sgt v_38 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_38 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_39)) v_73);
      let v_75 <- eval (concat (mux (sgt v_34 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_34 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_35)) v_74);
      let v_76 <- eval (concat (mux (sgt v_30 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_30 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_31)) v_75);
      let v_77 <- eval (concat (mux (sgt v_26 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_26 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_27)) v_76);
      let v_78 <- eval (concat (mux (sgt v_22 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_22 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_23)) v_77);
      let v_79 <- eval (concat (mux (sgt v_18 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_18 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_19)) v_78);
      let v_80 <- eval (concat (mux (sgt v_14 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_14 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_15)) v_79);
      let v_81 <- eval (concat (mux (sgt v_10 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_10 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_11)) v_80);
      let v_82 <- eval (concat (mux (sgt v_6 (expression.bv_nat 16 127)) (expression.bv_nat 8 127) (mux (slt v_6 (expression.bv_nat 16 65408)) (expression.bv_nat 8 128) v_7)) v_81);
      setRegister (lhs.of_reg xmm_1) v_82;
      pure ()
     action

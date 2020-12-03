def pmaddubsw : instruction :=
  definst "pmaddubsw" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 8)) <- eval (extract v_3 8 16);
      let v_5 <- getRegister (lhs.of_reg xmm_1);
      let (v_6 : expression (bv 8)) <- eval (extract v_5 8 16);
      let v_7 <- eval (concat (expression.bv_nat 8 0) v_6);
      let (v_8 : expression (bv 8)) <- eval (extract v_3 0 8);
      let (v_9 : expression (bv 8)) <- eval (extract v_5 0 8);
      let v_10 <- eval (concat (expression.bv_nat 8 0) v_9);
      let v_11 <- eval (add (sext (mul (sext v_4 16) v_7) 32) (sext (mul (sext v_8 16) v_10) 32));
      let (v_12 : expression (bv 16)) <- eval (extract v_11 16 32);
      let (v_13 : expression (bv 8)) <- eval (extract v_3 24 32);
      let (v_14 : expression (bv 8)) <- eval (extract v_5 24 32);
      let v_15 <- eval (concat (expression.bv_nat 8 0) v_14);
      let (v_16 : expression (bv 8)) <- eval (extract v_3 16 24);
      let (v_17 : expression (bv 8)) <- eval (extract v_5 16 24);
      let v_18 <- eval (concat (expression.bv_nat 8 0) v_17);
      let v_19 <- eval (add (sext (mul (sext v_13 16) v_15) 32) (sext (mul (sext v_16 16) v_18) 32));
      let (v_20 : expression (bv 16)) <- eval (extract v_19 16 32);
      let (v_21 : expression (bv 8)) <- eval (extract v_3 40 48);
      let (v_22 : expression (bv 8)) <- eval (extract v_5 40 48);
      let v_23 <- eval (concat (expression.bv_nat 8 0) v_22);
      let (v_24 : expression (bv 8)) <- eval (extract v_3 32 40);
      let (v_25 : expression (bv 8)) <- eval (extract v_5 32 40);
      let v_26 <- eval (concat (expression.bv_nat 8 0) v_25);
      let v_27 <- eval (add (sext (mul (sext v_21 16) v_23) 32) (sext (mul (sext v_24 16) v_26) 32));
      let (v_28 : expression (bv 16)) <- eval (extract v_27 16 32);
      let (v_29 : expression (bv 8)) <- eval (extract v_3 56 64);
      let (v_30 : expression (bv 8)) <- eval (extract v_5 56 64);
      let v_31 <- eval (concat (expression.bv_nat 8 0) v_30);
      let (v_32 : expression (bv 8)) <- eval (extract v_3 48 56);
      let (v_33 : expression (bv 8)) <- eval (extract v_5 48 56);
      let v_34 <- eval (concat (expression.bv_nat 8 0) v_33);
      let v_35 <- eval (add (sext (mul (sext v_29 16) v_31) 32) (sext (mul (sext v_32 16) v_34) 32));
      let (v_36 : expression (bv 16)) <- eval (extract v_35 16 32);
      let (v_37 : expression (bv 8)) <- eval (extract v_3 72 80);
      let (v_38 : expression (bv 8)) <- eval (extract v_5 72 80);
      let v_39 <- eval (concat (expression.bv_nat 8 0) v_38);
      let (v_40 : expression (bv 8)) <- eval (extract v_3 64 72);
      let (v_41 : expression (bv 8)) <- eval (extract v_5 64 72);
      let v_42 <- eval (concat (expression.bv_nat 8 0) v_41);
      let v_43 <- eval (add (sext (mul (sext v_37 16) v_39) 32) (sext (mul (sext v_40 16) v_42) 32));
      let (v_44 : expression (bv 16)) <- eval (extract v_43 16 32);
      let (v_45 : expression (bv 8)) <- eval (extract v_3 88 96);
      let (v_46 : expression (bv 8)) <- eval (extract v_5 88 96);
      let v_47 <- eval (concat (expression.bv_nat 8 0) v_46);
      let (v_48 : expression (bv 8)) <- eval (extract v_3 80 88);
      let (v_49 : expression (bv 8)) <- eval (extract v_5 80 88);
      let v_50 <- eval (concat (expression.bv_nat 8 0) v_49);
      let v_51 <- eval (add (sext (mul (sext v_45 16) v_47) 32) (sext (mul (sext v_48 16) v_50) 32));
      let (v_52 : expression (bv 16)) <- eval (extract v_51 16 32);
      let (v_53 : expression (bv 8)) <- eval (extract v_3 104 112);
      let (v_54 : expression (bv 8)) <- eval (extract v_5 104 112);
      let v_55 <- eval (concat (expression.bv_nat 8 0) v_54);
      let (v_56 : expression (bv 8)) <- eval (extract v_3 96 104);
      let (v_57 : expression (bv 8)) <- eval (extract v_5 96 104);
      let v_58 <- eval (concat (expression.bv_nat 8 0) v_57);
      let v_59 <- eval (add (sext (mul (sext v_53 16) v_55) 32) (sext (mul (sext v_56 16) v_58) 32));
      let (v_60 : expression (bv 16)) <- eval (extract v_59 16 32);
      let (v_61 : expression (bv 8)) <- eval (extract v_3 120 128);
      let (v_62 : expression (bv 8)) <- eval (extract v_5 120 128);
      let v_63 <- eval (concat (expression.bv_nat 8 0) v_62);
      let (v_64 : expression (bv 8)) <- eval (extract v_3 112 120);
      let (v_65 : expression (bv 8)) <- eval (extract v_5 112 120);
      let v_66 <- eval (concat (expression.bv_nat 8 0) v_65);
      let v_67 <- eval (add (sext (mul (sext v_61 16) v_63) 32) (sext (mul (sext v_64 16) v_66) 32));
      let (v_68 : expression (bv 16)) <- eval (extract v_67 16 32);
      let v_69 <- eval (concat (mux (sgt v_59 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_59 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_60)) (mux (sgt v_67 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_67 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_68)));
      let v_70 <- eval (concat (mux (sgt v_51 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_51 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_52)) v_69);
      let v_71 <- eval (concat (mux (sgt v_43 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_43 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_44)) v_70);
      let v_72 <- eval (concat (mux (sgt v_35 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_35 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_36)) v_71);
      let v_73 <- eval (concat (mux (sgt v_27 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_27 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_28)) v_72);
      let v_74 <- eval (concat (mux (sgt v_19 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_19 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_20)) v_73);
      let v_75 <- eval (concat (mux (sgt v_11 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_11 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_12)) v_74);
      setRegister (lhs.of_reg xmm_1) v_75;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 8)) <- eval (extract v_2 8 16);
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 8)) <- eval (extract v_4 8 16);
      let v_6 <- eval (concat (expression.bv_nat 8 0) v_5);
      let (v_7 : expression (bv 8)) <- eval (extract v_2 0 8);
      let (v_8 : expression (bv 8)) <- eval (extract v_4 0 8);
      let v_9 <- eval (concat (expression.bv_nat 8 0) v_8);
      let v_10 <- eval (add (sext (mul (sext v_3 16) v_6) 32) (sext (mul (sext v_7 16) v_9) 32));
      let (v_11 : expression (bv 16)) <- eval (extract v_10 16 32);
      let (v_12 : expression (bv 8)) <- eval (extract v_2 24 32);
      let (v_13 : expression (bv 8)) <- eval (extract v_4 24 32);
      let v_14 <- eval (concat (expression.bv_nat 8 0) v_13);
      let (v_15 : expression (bv 8)) <- eval (extract v_2 16 24);
      let (v_16 : expression (bv 8)) <- eval (extract v_4 16 24);
      let v_17 <- eval (concat (expression.bv_nat 8 0) v_16);
      let v_18 <- eval (add (sext (mul (sext v_12 16) v_14) 32) (sext (mul (sext v_15 16) v_17) 32));
      let (v_19 : expression (bv 16)) <- eval (extract v_18 16 32);
      let (v_20 : expression (bv 8)) <- eval (extract v_2 40 48);
      let (v_21 : expression (bv 8)) <- eval (extract v_4 40 48);
      let v_22 <- eval (concat (expression.bv_nat 8 0) v_21);
      let (v_23 : expression (bv 8)) <- eval (extract v_2 32 40);
      let (v_24 : expression (bv 8)) <- eval (extract v_4 32 40);
      let v_25 <- eval (concat (expression.bv_nat 8 0) v_24);
      let v_26 <- eval (add (sext (mul (sext v_20 16) v_22) 32) (sext (mul (sext v_23 16) v_25) 32));
      let (v_27 : expression (bv 16)) <- eval (extract v_26 16 32);
      let (v_28 : expression (bv 8)) <- eval (extract v_2 56 64);
      let (v_29 : expression (bv 8)) <- eval (extract v_4 56 64);
      let v_30 <- eval (concat (expression.bv_nat 8 0) v_29);
      let (v_31 : expression (bv 8)) <- eval (extract v_2 48 56);
      let (v_32 : expression (bv 8)) <- eval (extract v_4 48 56);
      let v_33 <- eval (concat (expression.bv_nat 8 0) v_32);
      let v_34 <- eval (add (sext (mul (sext v_28 16) v_30) 32) (sext (mul (sext v_31 16) v_33) 32));
      let (v_35 : expression (bv 16)) <- eval (extract v_34 16 32);
      let (v_36 : expression (bv 8)) <- eval (extract v_2 72 80);
      let (v_37 : expression (bv 8)) <- eval (extract v_4 72 80);
      let v_38 <- eval (concat (expression.bv_nat 8 0) v_37);
      let (v_39 : expression (bv 8)) <- eval (extract v_2 64 72);
      let (v_40 : expression (bv 8)) <- eval (extract v_4 64 72);
      let v_41 <- eval (concat (expression.bv_nat 8 0) v_40);
      let v_42 <- eval (add (sext (mul (sext v_36 16) v_38) 32) (sext (mul (sext v_39 16) v_41) 32));
      let (v_43 : expression (bv 16)) <- eval (extract v_42 16 32);
      let (v_44 : expression (bv 8)) <- eval (extract v_2 88 96);
      let (v_45 : expression (bv 8)) <- eval (extract v_4 88 96);
      let v_46 <- eval (concat (expression.bv_nat 8 0) v_45);
      let (v_47 : expression (bv 8)) <- eval (extract v_2 80 88);
      let (v_48 : expression (bv 8)) <- eval (extract v_4 80 88);
      let v_49 <- eval (concat (expression.bv_nat 8 0) v_48);
      let v_50 <- eval (add (sext (mul (sext v_44 16) v_46) 32) (sext (mul (sext v_47 16) v_49) 32));
      let (v_51 : expression (bv 16)) <- eval (extract v_50 16 32);
      let (v_52 : expression (bv 8)) <- eval (extract v_2 104 112);
      let (v_53 : expression (bv 8)) <- eval (extract v_4 104 112);
      let v_54 <- eval (concat (expression.bv_nat 8 0) v_53);
      let (v_55 : expression (bv 8)) <- eval (extract v_2 96 104);
      let (v_56 : expression (bv 8)) <- eval (extract v_4 96 104);
      let v_57 <- eval (concat (expression.bv_nat 8 0) v_56);
      let v_58 <- eval (add (sext (mul (sext v_52 16) v_54) 32) (sext (mul (sext v_55 16) v_57) 32));
      let (v_59 : expression (bv 16)) <- eval (extract v_58 16 32);
      let (v_60 : expression (bv 8)) <- eval (extract v_2 120 128);
      let (v_61 : expression (bv 8)) <- eval (extract v_4 120 128);
      let v_62 <- eval (concat (expression.bv_nat 8 0) v_61);
      let (v_63 : expression (bv 8)) <- eval (extract v_2 112 120);
      let (v_64 : expression (bv 8)) <- eval (extract v_4 112 120);
      let v_65 <- eval (concat (expression.bv_nat 8 0) v_64);
      let v_66 <- eval (add (sext (mul (sext v_60 16) v_62) 32) (sext (mul (sext v_63 16) v_65) 32));
      let (v_67 : expression (bv 16)) <- eval (extract v_66 16 32);
      let v_68 <- eval (concat (mux (sgt v_58 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_58 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_59)) (mux (sgt v_66 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_66 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_67)));
      let v_69 <- eval (concat (mux (sgt v_50 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_50 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_51)) v_68);
      let v_70 <- eval (concat (mux (sgt v_42 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_42 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_43)) v_69);
      let v_71 <- eval (concat (mux (sgt v_34 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_34 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_35)) v_70);
      let v_72 <- eval (concat (mux (sgt v_26 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_26 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_27)) v_71);
      let v_73 <- eval (concat (mux (sgt v_18 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_18 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_19)) v_72);
      let v_74 <- eval (concat (mux (sgt v_10 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_10 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) v_11)) v_73);
      setRegister (lhs.of_reg xmm_1) v_74;
      pure ()
     action

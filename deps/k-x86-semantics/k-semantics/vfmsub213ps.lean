def vfmsub213ps : instruction :=
  definst "vfmsub213ps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- getRegister (lhs.of_reg xmm_2);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let v_9 <- evaluateAddress mem_0;
      let v_10 <- load v_9 16;
      let (v_11 : expression (bv 32)) <- eval (extract v_10 0 32);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_10 32 64);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      let (v_19 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      let (v_21 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_22 <- eval (bv_bitcast_to_fp float_class.fp32 v_21);
      let (v_23 : expression (bv 32)) <- eval (extract v_10 64 96);
      let v_24 <- eval (bv_bitcast_to_fp float_class.fp32 v_23);
      let (v_25 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_26 <- eval (bv_bitcast_to_fp float_class.fp32 v_25);
      let (v_27 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_28 <- eval (bv_bitcast_to_fp float_class.fp32 v_27);
      let (v_29 : expression (bv 32)) <- eval (extract v_10 96 128);
      let v_30 <- eval (bv_bitcast_to_fp float_class.fp32 v_29);
      let v_31 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_20 v_22) v_24) 32) (fp_bitcast_to_bv (fp_sub (fp_mul v_26 v_28) v_30) 32));
      let v_32 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_14 v_16) v_18) 32) v_31);
      let v_33 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_8) v_12) 32) v_32);
      setRegister (lhs.of_reg xmm_2) v_33;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- getRegister (lhs.of_reg ymm_2);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let v_9 <- evaluateAddress mem_0;
      let v_10 <- load v_9 32;
      let (v_11 : expression (bv 32)) <- eval (extract v_10 0 32);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_10 32 64);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      let v_19 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_8) v_12) 32) (fp_bitcast_to_bv (fp_sub (fp_mul v_14 v_16) v_18) 32));
      let (v_20 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      let (v_22 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_23 <- eval (bv_bitcast_to_fp float_class.fp32 v_22);
      let (v_24 : expression (bv 32)) <- eval (extract v_10 64 96);
      let v_25 <- eval (bv_bitcast_to_fp float_class.fp32 v_24);
      let (v_26 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_27 <- eval (bv_bitcast_to_fp float_class.fp32 v_26);
      let (v_28 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_29 <- eval (bv_bitcast_to_fp float_class.fp32 v_28);
      let (v_30 : expression (bv 32)) <- eval (extract v_10 96 128);
      let v_31 <- eval (bv_bitcast_to_fp float_class.fp32 v_30);
      let (v_32 : expression (bv 32)) <- eval (extract v_3 128 160);
      let v_33 <- eval (bv_bitcast_to_fp float_class.fp32 v_32);
      let (v_34 : expression (bv 32)) <- eval (extract v_6 128 160);
      let v_35 <- eval (bv_bitcast_to_fp float_class.fp32 v_34);
      let (v_36 : expression (bv 32)) <- eval (extract v_10 128 160);
      let v_37 <- eval (bv_bitcast_to_fp float_class.fp32 v_36);
      let (v_38 : expression (bv 32)) <- eval (extract v_3 160 192);
      let v_39 <- eval (bv_bitcast_to_fp float_class.fp32 v_38);
      let (v_40 : expression (bv 32)) <- eval (extract v_6 160 192);
      let v_41 <- eval (bv_bitcast_to_fp float_class.fp32 v_40);
      let (v_42 : expression (bv 32)) <- eval (extract v_10 160 192);
      let v_43 <- eval (bv_bitcast_to_fp float_class.fp32 v_42);
      let (v_44 : expression (bv 32)) <- eval (extract v_3 192 224);
      let v_45 <- eval (bv_bitcast_to_fp float_class.fp32 v_44);
      let (v_46 : expression (bv 32)) <- eval (extract v_6 192 224);
      let v_47 <- eval (bv_bitcast_to_fp float_class.fp32 v_46);
      let (v_48 : expression (bv 32)) <- eval (extract v_10 192 224);
      let v_49 <- eval (bv_bitcast_to_fp float_class.fp32 v_48);
      let (v_50 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_51 <- eval (bv_bitcast_to_fp float_class.fp32 v_50);
      let (v_52 : expression (bv 32)) <- eval (extract v_6 224 256);
      let v_53 <- eval (bv_bitcast_to_fp float_class.fp32 v_52);
      let (v_54 : expression (bv 32)) <- eval (extract v_10 224 256);
      let v_55 <- eval (bv_bitcast_to_fp float_class.fp32 v_54);
      let v_56 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_45 v_47) v_49) 32) (fp_bitcast_to_bv (fp_sub (fp_mul v_51 v_53) v_55) 32));
      let v_57 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_39 v_41) v_43) 32) v_56);
      let v_58 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_33 v_35) v_37) 32) v_57);
      let v_59 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_27 v_29) v_31) 32) v_58);
      let v_60 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_21 v_23) v_25) 32) v_59);
      let v_61 <- eval (concat v_19 v_60);
      setRegister (lhs.of_reg ymm_2) v_61;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- getRegister (lhs.of_reg xmm_2);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let v_9 <- getRegister (lhs.of_reg xmm_0);
      let (v_10 : expression (bv 32)) <- eval (extract v_9 0 32);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let (v_14 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_9 32 64);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      let (v_18 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      let (v_20 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      let (v_22 : expression (bv 32)) <- eval (extract v_9 64 96);
      let v_23 <- eval (bv_bitcast_to_fp float_class.fp32 v_22);
      let (v_24 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_25 <- eval (bv_bitcast_to_fp float_class.fp32 v_24);
      let (v_26 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_27 <- eval (bv_bitcast_to_fp float_class.fp32 v_26);
      let (v_28 : expression (bv 32)) <- eval (extract v_9 96 128);
      let v_29 <- eval (bv_bitcast_to_fp float_class.fp32 v_28);
      let v_30 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_19 v_21) v_23) 32) (fp_bitcast_to_bv (fp_sub (fp_mul v_25 v_27) v_29) 32));
      let v_31 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_13 v_15) v_17) 32) v_30);
      let v_32 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_8) v_11) 32) v_31);
      setRegister (lhs.of_reg xmm_2) v_32;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- getRegister (lhs.of_reg ymm_2);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let v_9 <- getRegister (lhs.of_reg ymm_0);
      let (v_10 : expression (bv 32)) <- eval (extract v_9 0 32);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let (v_14 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_9 32 64);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      let v_18 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_8) v_11) 32) (fp_bitcast_to_bv (fp_sub (fp_mul v_13 v_15) v_17) 32));
      let (v_19 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      let (v_21 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_22 <- eval (bv_bitcast_to_fp float_class.fp32 v_21);
      let (v_23 : expression (bv 32)) <- eval (extract v_9 64 96);
      let v_24 <- eval (bv_bitcast_to_fp float_class.fp32 v_23);
      let (v_25 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_26 <- eval (bv_bitcast_to_fp float_class.fp32 v_25);
      let (v_27 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_28 <- eval (bv_bitcast_to_fp float_class.fp32 v_27);
      let (v_29 : expression (bv 32)) <- eval (extract v_9 96 128);
      let v_30 <- eval (bv_bitcast_to_fp float_class.fp32 v_29);
      let (v_31 : expression (bv 32)) <- eval (extract v_3 128 160);
      let v_32 <- eval (bv_bitcast_to_fp float_class.fp32 v_31);
      let (v_33 : expression (bv 32)) <- eval (extract v_6 128 160);
      let v_34 <- eval (bv_bitcast_to_fp float_class.fp32 v_33);
      let (v_35 : expression (bv 32)) <- eval (extract v_9 128 160);
      let v_36 <- eval (bv_bitcast_to_fp float_class.fp32 v_35);
      let (v_37 : expression (bv 32)) <- eval (extract v_3 160 192);
      let v_38 <- eval (bv_bitcast_to_fp float_class.fp32 v_37);
      let (v_39 : expression (bv 32)) <- eval (extract v_6 160 192);
      let v_40 <- eval (bv_bitcast_to_fp float_class.fp32 v_39);
      let (v_41 : expression (bv 32)) <- eval (extract v_9 160 192);
      let v_42 <- eval (bv_bitcast_to_fp float_class.fp32 v_41);
      let (v_43 : expression (bv 32)) <- eval (extract v_3 192 224);
      let v_44 <- eval (bv_bitcast_to_fp float_class.fp32 v_43);
      let (v_45 : expression (bv 32)) <- eval (extract v_6 192 224);
      let v_46 <- eval (bv_bitcast_to_fp float_class.fp32 v_45);
      let (v_47 : expression (bv 32)) <- eval (extract v_9 192 224);
      let v_48 <- eval (bv_bitcast_to_fp float_class.fp32 v_47);
      let (v_49 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_50 <- eval (bv_bitcast_to_fp float_class.fp32 v_49);
      let (v_51 : expression (bv 32)) <- eval (extract v_6 224 256);
      let v_52 <- eval (bv_bitcast_to_fp float_class.fp32 v_51);
      let (v_53 : expression (bv 32)) <- eval (extract v_9 224 256);
      let v_54 <- eval (bv_bitcast_to_fp float_class.fp32 v_53);
      let v_55 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_44 v_46) v_48) 32) (fp_bitcast_to_bv (fp_sub (fp_mul v_50 v_52) v_54) 32));
      let v_56 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_38 v_40) v_42) 32) v_55);
      let v_57 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_32 v_34) v_36) 32) v_56);
      let v_58 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_26 v_28) v_30) 32) v_57);
      let v_59 <- eval (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_20 v_22) v_24) 32) v_58);
      let v_60 <- eval (concat v_18 v_59);
      setRegister (lhs.of_reg ymm_2) v_60;
      pure ()
     action
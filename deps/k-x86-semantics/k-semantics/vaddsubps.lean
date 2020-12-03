def vaddsubps : instruction :=
  definst "vaddsubps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 16;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_7 32 64);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let v_14 <- eval (concat (fp_bitcast_to_bv (fp_add v_5 v_9) 32) (fp_bitcast_to_bv (fp_sub v_11 v_13) 32));
      let (v_15 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_7 64 96);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      let (v_19 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      let (v_21 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_22 <- eval (bv_bitcast_to_fp float_class.fp32 v_21);
      let v_23 <- eval (concat (fp_bitcast_to_bv (fp_add v_16 v_18) 32) (fp_bitcast_to_bv (fp_sub v_20 v_22) 32));
      let v_24 <- eval (concat v_14 v_23);
      setRegister (lhs.of_reg xmm_2) v_24;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- evaluateAddress mem_0;
      let v_7 <- load v_6 32;
      let (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_7 32 64);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let v_14 <- eval (concat (fp_bitcast_to_bv (fp_add v_5 v_9) 32) (fp_bitcast_to_bv (fp_sub v_11 v_13) 32));
      let (v_15 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_7 64 96);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      let (v_19 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      let (v_21 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_22 <- eval (bv_bitcast_to_fp float_class.fp32 v_21);
      let v_23 <- eval (concat (fp_bitcast_to_bv (fp_add v_16 v_18) 32) (fp_bitcast_to_bv (fp_sub v_20 v_22) 32));
      let (v_24 : expression (bv 32)) <- eval (extract v_3 128 160);
      let v_25 <- eval (bv_bitcast_to_fp float_class.fp32 v_24);
      let (v_26 : expression (bv 32)) <- eval (extract v_7 128 160);
      let v_27 <- eval (bv_bitcast_to_fp float_class.fp32 v_26);
      let (v_28 : expression (bv 32)) <- eval (extract v_3 160 192);
      let v_29 <- eval (bv_bitcast_to_fp float_class.fp32 v_28);
      let (v_30 : expression (bv 32)) <- eval (extract v_7 160 192);
      let v_31 <- eval (bv_bitcast_to_fp float_class.fp32 v_30);
      let v_32 <- eval (concat (fp_bitcast_to_bv (fp_add v_25 v_27) 32) (fp_bitcast_to_bv (fp_sub v_29 v_31) 32));
      let (v_33 : expression (bv 32)) <- eval (extract v_3 192 224);
      let v_34 <- eval (bv_bitcast_to_fp float_class.fp32 v_33);
      let (v_35 : expression (bv 32)) <- eval (extract v_7 192 224);
      let v_36 <- eval (bv_bitcast_to_fp float_class.fp32 v_35);
      let (v_37 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_38 <- eval (bv_bitcast_to_fp float_class.fp32 v_37);
      let (v_39 : expression (bv 32)) <- eval (extract v_7 224 256);
      let v_40 <- eval (bv_bitcast_to_fp float_class.fp32 v_39);
      let v_41 <- eval (concat (fp_bitcast_to_bv (fp_add v_34 v_36) 32) (fp_bitcast_to_bv (fp_sub v_38 v_40) 32));
      let v_42 <- eval (concat v_32 v_41);
      let v_43 <- eval (concat v_23 v_42);
      let v_44 <- eval (concat v_14 v_43);
      setRegister (lhs.of_reg ymm_2) v_44;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- getRegister (lhs.of_reg xmm_0);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let v_13 <- eval (concat (fp_bitcast_to_bv (fp_add v_5 v_8) 32) (fp_bitcast_to_bv (fp_sub v_10 v_12) 32));
      let (v_14 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      let (v_18 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      let (v_20 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      let v_22 <- eval (concat (fp_bitcast_to_bv (fp_add v_15 v_17) 32) (fp_bitcast_to_bv (fp_sub v_19 v_21) 32));
      let v_23 <- eval (concat v_13 v_22);
      setRegister (lhs.of_reg xmm_2) v_23;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- getRegister (lhs.of_reg ymm_0);
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let v_13 <- eval (concat (fp_bitcast_to_bv (fp_add v_5 v_8) 32) (fp_bitcast_to_bv (fp_sub v_10 v_12) 32));
      let (v_14 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      let (v_18 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      let (v_20 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      let v_22 <- eval (concat (fp_bitcast_to_bv (fp_add v_15 v_17) 32) (fp_bitcast_to_bv (fp_sub v_19 v_21) 32));
      let (v_23 : expression (bv 32)) <- eval (extract v_3 128 160);
      let v_24 <- eval (bv_bitcast_to_fp float_class.fp32 v_23);
      let (v_25 : expression (bv 32)) <- eval (extract v_6 128 160);
      let v_26 <- eval (bv_bitcast_to_fp float_class.fp32 v_25);
      let (v_27 : expression (bv 32)) <- eval (extract v_3 160 192);
      let v_28 <- eval (bv_bitcast_to_fp float_class.fp32 v_27);
      let (v_29 : expression (bv 32)) <- eval (extract v_6 160 192);
      let v_30 <- eval (bv_bitcast_to_fp float_class.fp32 v_29);
      let v_31 <- eval (concat (fp_bitcast_to_bv (fp_add v_24 v_26) 32) (fp_bitcast_to_bv (fp_sub v_28 v_30) 32));
      let (v_32 : expression (bv 32)) <- eval (extract v_3 192 224);
      let v_33 <- eval (bv_bitcast_to_fp float_class.fp32 v_32);
      let (v_34 : expression (bv 32)) <- eval (extract v_6 192 224);
      let v_35 <- eval (bv_bitcast_to_fp float_class.fp32 v_34);
      let (v_36 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_37 <- eval (bv_bitcast_to_fp float_class.fp32 v_36);
      let (v_38 : expression (bv 32)) <- eval (extract v_6 224 256);
      let v_39 <- eval (bv_bitcast_to_fp float_class.fp32 v_38);
      let v_40 <- eval (concat (fp_bitcast_to_bv (fp_add v_33 v_35) 32) (fp_bitcast_to_bv (fp_sub v_37 v_39) 32));
      let v_41 <- eval (concat v_31 v_40);
      let v_42 <- eval (concat v_22 v_41);
      let v_43 <- eval (concat v_13 v_42);
      setRegister (lhs.of_reg ymm_2) v_43;
      pure ()
     action

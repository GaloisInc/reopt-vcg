def vcvtph2ps : instruction :=
  definst "vcvtph2ps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp16 v_4);
      let v_6 <- eval (fp_round float_class.fp32 v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp16 v_7);
      let v_9 <- eval (fp_round float_class.fp32 v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp16 v_10);
      let v_12 <- eval (fp_round float_class.fp32 v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp16 v_13);
      let v_15 <- eval (fp_round float_class.fp32 v_14);
      let v_16 <- eval (concat (fp_bitcast_to_bv v_12 32) (fp_bitcast_to_bv v_15 32));
      let v_17 <- eval (concat (fp_bitcast_to_bv v_9 32) v_16);
      let v_18 <- eval (concat (fp_bitcast_to_bv v_6 32) v_17);
      setRegister (lhs.of_reg xmm_1) v_18;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp16 v_4);
      let v_6 <- eval (fp_round float_class.fp32 v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp16 v_7);
      let v_9 <- eval (fp_round float_class.fp32 v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp16 v_10);
      let v_12 <- eval (fp_round float_class.fp32 v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp16 v_13);
      let v_15 <- eval (fp_round float_class.fp32 v_14);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp16 v_16);
      let v_18 <- eval (fp_round float_class.fp32 v_17);
      let (v_19 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp16 v_19);
      let v_21 <- eval (fp_round float_class.fp32 v_20);
      let (v_22 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_23 <- eval (bv_bitcast_to_fp float_class.fp16 v_22);
      let v_24 <- eval (fp_round float_class.fp32 v_23);
      let (v_25 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_26 <- eval (bv_bitcast_to_fp float_class.fp16 v_25);
      let v_27 <- eval (fp_round float_class.fp32 v_26);
      let v_28 <- eval (concat (fp_bitcast_to_bv v_24 32) (fp_bitcast_to_bv v_27 32));
      let v_29 <- eval (concat (fp_bitcast_to_bv v_21 32) v_28);
      let v_30 <- eval (concat (fp_bitcast_to_bv v_18 32) v_29);
      let v_31 <- eval (concat (fp_bitcast_to_bv v_15 32) v_30);
      let v_32 <- eval (concat (fp_bitcast_to_bv v_12 32) v_31);
      let v_33 <- eval (concat (fp_bitcast_to_bv v_9 32) v_32);
      let v_34 <- eval (concat (fp_bitcast_to_bv v_6 32) v_33);
      setRegister (lhs.of_reg ymm_1) v_34;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp16 v_3);
      let v_5 <- eval (fp_round float_class.fp32 v_4);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 80 96);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp16 v_6);
      let v_8 <- eval (fp_round float_class.fp32 v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 96 112);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp16 v_9);
      let v_11 <- eval (fp_round float_class.fp32 v_10);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp16 v_12);
      let v_14 <- eval (fp_round float_class.fp32 v_13);
      let v_15 <- eval (concat (fp_bitcast_to_bv v_11 32) (fp_bitcast_to_bv v_14 32));
      let v_16 <- eval (concat (fp_bitcast_to_bv v_8 32) v_15);
      let v_17 <- eval (concat (fp_bitcast_to_bv v_5 32) v_16);
      setRegister (lhs.of_reg xmm_1) v_17;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp16 v_3);
      let v_5 <- eval (fp_round float_class.fp32 v_4);
      let (v_6 : expression (bv 16)) <- eval (extract v_2 16 32);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp16 v_6);
      let v_8 <- eval (fp_round float_class.fp32 v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 32 48);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp16 v_9);
      let v_11 <- eval (fp_round float_class.fp32 v_10);
      let (v_12 : expression (bv 16)) <- eval (extract v_2 48 64);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp16 v_12);
      let v_14 <- eval (fp_round float_class.fp32 v_13);
      let (v_15 : expression (bv 16)) <- eval (extract v_2 64 80);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp16 v_15);
      let v_17 <- eval (fp_round float_class.fp32 v_16);
      let (v_18 : expression (bv 16)) <- eval (extract v_2 80 96);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp16 v_18);
      let v_20 <- eval (fp_round float_class.fp32 v_19);
      let (v_21 : expression (bv 16)) <- eval (extract v_2 96 112);
      let v_22 <- eval (bv_bitcast_to_fp float_class.fp16 v_21);
      let v_23 <- eval (fp_round float_class.fp32 v_22);
      let (v_24 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_25 <- eval (bv_bitcast_to_fp float_class.fp16 v_24);
      let v_26 <- eval (fp_round float_class.fp32 v_25);
      let v_27 <- eval (concat (fp_bitcast_to_bv v_23 32) (fp_bitcast_to_bv v_26 32));
      let v_28 <- eval (concat (fp_bitcast_to_bv v_20 32) v_27);
      let v_29 <- eval (concat (fp_bitcast_to_bv v_17 32) v_28);
      let v_30 <- eval (concat (fp_bitcast_to_bv v_14 32) v_29);
      let v_31 <- eval (concat (fp_bitcast_to_bv v_11 32) v_30);
      let v_32 <- eval (concat (fp_bitcast_to_bv v_8 32) v_31);
      let v_33 <- eval (concat (fp_bitcast_to_bv v_5 32) v_32);
      setRegister (lhs.of_reg ymm_1) v_33;
      pure ()
     action

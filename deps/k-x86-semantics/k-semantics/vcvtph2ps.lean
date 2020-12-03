def vcvtph2ps : instruction :=
  definst "vcvtph2ps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 8;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp16 v_4);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp16 v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp16 v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp16 v_10);
      let v_12 <- eval (concat (fp_bitcast_to_bv (fp_round v_9 24 8) 32) (fp_bitcast_to_bv (fp_round v_11 24 8) 32));
      let v_13 <- eval (concat (fp_bitcast_to_bv (fp_round v_7 24 8) 32) v_12);
      let v_14 <- eval (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) v_13);
      setRegister (lhs.of_reg xmm_1) v_14;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp16 v_4);
      let (v_6 : expression (bv 16)) <- eval (extract v_3 16 32);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp16 v_6);
      let (v_8 : expression (bv 16)) <- eval (extract v_3 32 48);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp16 v_8);
      let (v_10 : expression (bv 16)) <- eval (extract v_3 48 64);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp16 v_10);
      let (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp16 v_12);
      let (v_14 : expression (bv 16)) <- eval (extract v_3 80 96);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp16 v_14);
      let (v_16 : expression (bv 16)) <- eval (extract v_3 96 112);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp16 v_16);
      let (v_18 : expression (bv 16)) <- eval (extract v_3 112 128);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp16 v_18);
      let v_20 <- eval (concat (fp_bitcast_to_bv (fp_round v_17 24 8) 32) (fp_bitcast_to_bv (fp_round v_19 24 8) 32));
      let v_21 <- eval (concat (fp_bitcast_to_bv (fp_round v_15 24 8) 32) v_20);
      let v_22 <- eval (concat (fp_bitcast_to_bv (fp_round v_13 24 8) 32) v_21);
      let v_23 <- eval (concat (fp_bitcast_to_bv (fp_round v_11 24 8) 32) v_22);
      let v_24 <- eval (concat (fp_bitcast_to_bv (fp_round v_9 24 8) 32) v_23);
      let v_25 <- eval (concat (fp_bitcast_to_bv (fp_round v_7 24 8) 32) v_24);
      let v_26 <- eval (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) v_25);
      setRegister (lhs.of_reg ymm_1) v_26;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp16 v_3);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 80 96);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp16 v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 96 112);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp16 v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp16 v_9);
      let v_11 <- eval (concat (fp_bitcast_to_bv (fp_round v_8 24 8) 32) (fp_bitcast_to_bv (fp_round v_10 24 8) 32));
      let v_12 <- eval (concat (fp_bitcast_to_bv (fp_round v_6 24 8) 32) v_11);
      let v_13 <- eval (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) v_12);
      setRegister (lhs.of_reg xmm_1) v_13;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp16 v_3);
      let (v_5 : expression (bv 16)) <- eval (extract v_2 16 32);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp16 v_5);
      let (v_7 : expression (bv 16)) <- eval (extract v_2 32 48);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp16 v_7);
      let (v_9 : expression (bv 16)) <- eval (extract v_2 48 64);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp16 v_9);
      let (v_11 : expression (bv 16)) <- eval (extract v_2 64 80);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp16 v_11);
      let (v_13 : expression (bv 16)) <- eval (extract v_2 80 96);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp16 v_13);
      let (v_15 : expression (bv 16)) <- eval (extract v_2 96 112);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp16 v_15);
      let (v_17 : expression (bv 16)) <- eval (extract v_2 112 128);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp16 v_17);
      let v_19 <- eval (concat (fp_bitcast_to_bv (fp_round v_16 24 8) 32) (fp_bitcast_to_bv (fp_round v_18 24 8) 32));
      let v_20 <- eval (concat (fp_bitcast_to_bv (fp_round v_14 24 8) 32) v_19);
      let v_21 <- eval (concat (fp_bitcast_to_bv (fp_round v_12 24 8) 32) v_20);
      let v_22 <- eval (concat (fp_bitcast_to_bv (fp_round v_10 24 8) 32) v_21);
      let v_23 <- eval (concat (fp_bitcast_to_bv (fp_round v_8 24 8) 32) v_22);
      let v_24 <- eval (concat (fp_bitcast_to_bv (fp_round v_6 24 8) 32) v_23);
      let v_25 <- eval (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) v_24);
      setRegister (lhs.of_reg ymm_1) v_25;
      pure ()
     action

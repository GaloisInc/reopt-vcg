def vrcpps : instruction :=
  definst "vrcpps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let v_12 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_9) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_11) 32));
      let v_13 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_7) 32) v_12);
      let v_14 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_5) 32) v_13);
      setRegister (lhs.of_reg xmm_1) v_14;
      pure ()
     action;
    instr_pat $ fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 32;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_3 128 160);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let (v_14 : expression (bv 32)) <- eval (extract v_3 160 192);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_3 192 224);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      let (v_18 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      let v_20 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_17) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_19) 32));
      let v_21 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_15) 32) v_20);
      let v_22 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_13) 32) v_21);
      let v_23 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_11) 32) v_22);
      let v_24 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_9) 32) v_23);
      let v_25 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_7) 32) v_24);
      let v_26 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_5) 32) v_25);
      setRegister (lhs.of_reg ymm_1) v_26;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      let (v_7 : expression (bv 32)) <- eval (extract v_2 64 96);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let v_11 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_8) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_10) 32));
      let v_12 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_6) 32) v_11);
      let v_13 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_4) 32) v_12);
      setRegister (lhs.of_reg xmm_1) v_13;
      pure ()
     action;
    instr_pat $ fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg ymm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      let (v_7 : expression (bv 32)) <- eval (extract v_2 64 96);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_2 128 160);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let (v_13 : expression (bv 32)) <- eval (extract v_2 160 192);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_2 192 224);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_2 224 256);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      let v_19 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_16) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_18) 32));
      let v_20 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_14) 32) v_19);
      let v_21 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_12) 32) v_20);
      let v_22 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_10) 32) v_21);
      let v_23 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_8) 32) v_22);
      let v_24 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_6) 32) v_23);
      let v_25 <- eval (concat (fp_bitcast_to_bv (fp_div 1e+00 v_4) 32) v_24);
      setRegister (lhs.of_reg ymm_1) v_25;
      pure ()
     action

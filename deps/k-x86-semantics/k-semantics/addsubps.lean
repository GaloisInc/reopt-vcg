def addsubps : instruction :=
  definst "addsubps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      let v_5 <- evaluateAddress mem_0;
      let v_6 <- load v_5 16;
      let (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_6 32 64);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let v_13 <- eval (concat (fp_bitcast_to_bv (fp_add v_4 v_8) 32) (fp_bitcast_to_bv (fp_sub v_10 v_12) 32));
      let (v_14 : expression (bv 32)) <- eval (extract v_2 64 96);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_6 64 96);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      let (v_18 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      let (v_20 : expression (bv 32)) <- eval (extract v_6 96 128);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      let v_22 <- eval (concat (fp_bitcast_to_bv (fp_add v_15 v_17) 32) (fp_bitcast_to_bv (fp_sub v_19 v_21) 32));
      let v_23 <- eval (concat v_13 v_22);
      setRegister (lhs.of_reg xmm_1) v_23;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_1);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      let v_5 <- getRegister (lhs.of_reg xmm_0);
      let (v_6 : expression (bv 32)) <- eval (extract v_5 0 32);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_5 32 64);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let v_12 <- eval (concat (fp_bitcast_to_bv (fp_add v_4 v_7) 32) (fp_bitcast_to_bv (fp_sub v_9 v_11) 32));
      let (v_13 : expression (bv 32)) <- eval (extract v_2 64 96);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_5 64 96);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      let (v_19 : expression (bv 32)) <- eval (extract v_5 96 128);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      let v_21 <- eval (concat (fp_bitcast_to_bv (fp_add v_14 v_16) 32) (fp_bitcast_to_bv (fp_sub v_18 v_20) 32));
      let v_22 <- eval (concat v_12 v_21);
      setRegister (lhs.of_reg xmm_1) v_22;
      pure ()
     action

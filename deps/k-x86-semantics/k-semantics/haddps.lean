def haddps : instruction :=
  definst "haddps" $ do
    instr_pat $ fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- evaluateAddress mem_0;
      let v_3 <- load v_2 16;
      let (v_4 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let (v_6 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_7 <- eval (bv_bitcast_to_fp float_class.fp32 v_6);
      let (v_8 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let v_12 <- eval (concat (fp_bitcast_to_bv (fp_add v_5 v_7) 32) (fp_bitcast_to_bv (fp_add v_9 v_11) 32));
      let v_13 <- getRegister (lhs.of_reg xmm_1);
      let (v_14 : expression (bv 32)) <- eval (extract v_13 32 64);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_13 0 32);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      let v_18 <- eval (concat v_12 (fp_bitcast_to_bv (fp_add v_15 v_17) 32));
      let (v_19 : expression (bv 32)) <- eval (extract v_13 96 128);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      let (v_21 : expression (bv 32)) <- eval (extract v_13 64 96);
      let v_22 <- eval (bv_bitcast_to_fp float_class.fp32 v_21);
      let v_23 <- eval (concat v_18 (fp_bitcast_to_bv (fp_add v_20 v_22) 32));
      setRegister (lhs.of_reg xmm_1) v_23;
      pure ()
     action;
    instr_pat $ fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_2 <- getRegister (lhs.of_reg xmm_0);
      let (v_3 : expression (bv 32)) <- eval (extract v_2 32 64);
      let v_4 <- eval (bv_bitcast_to_fp float_class.fp32 v_3);
      let (v_5 : expression (bv 32)) <- eval (extract v_2 0 32);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      let (v_7 : expression (bv 32)) <- eval (extract v_2 96 128);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_2 64 96);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let v_11 <- eval (concat (fp_bitcast_to_bv (fp_add v_4 v_6) 32) (fp_bitcast_to_bv (fp_add v_8 v_10) 32));
      let v_12 <- getRegister (lhs.of_reg xmm_1);
      let (v_13 : expression (bv 32)) <- eval (extract v_12 32 64);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_12 0 32);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      let v_17 <- eval (concat v_11 (fp_bitcast_to_bv (fp_add v_14 v_16) 32));
      let (v_18 : expression (bv 32)) <- eval (extract v_12 96 128);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      let (v_20 : expression (bv 32)) <- eval (extract v_12 64 96);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      let v_22 <- eval (concat v_17 (fp_bitcast_to_bv (fp_add v_19 v_21) 32));
      setRegister (lhs.of_reg xmm_1) v_22;
      pure ()
     action

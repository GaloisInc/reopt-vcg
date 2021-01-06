def vcvtps2ph : instruction :=
  definst "vcvtps2ph" $ do
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (mem_2 : Mem) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_2;
      let v_4 <- getRegister (lhs.of_reg xmm_1);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      let v_7 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      let (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let v_14 <- eval (concat (fp_bitcast_to_bv (Float2Half v_11 v_7) 16) (fp_bitcast_to_bv (Float2Half v_13 v_7) 16));
      let v_15 <- eval (concat (fp_bitcast_to_bv (Float2Half v_9 v_7) 16) v_14);
      let v_16 <- eval (concat (fp_bitcast_to_bv (Float2Half v_6 v_7) 16) v_15);
      store v_3 v_16 8;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg xmm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      let (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let v_13 <- eval (concat (fp_bitcast_to_bv (Float2Half v_10 v_6) 16) (fp_bitcast_to_bv (Float2Half v_12 v_6) 16));
      let v_14 <- eval (concat (fp_bitcast_to_bv (Float2Half v_8 v_6) 16) v_13);
      let v_15 <- eval (concat (fp_bitcast_to_bv (Float2Half v_5 v_6) 16) v_14);
      let v_16 <- eval (concat (expression.bv_nat 64 0) v_15);
      setRegister (lhs.of_reg xmm_2) v_16;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (mem_2 : Mem) =>
     let action : semantics Unit := do
      let v_3 <- evaluateAddress mem_2;
      let v_4 <- getRegister (lhs.of_reg ymm_1);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      let v_7 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      let (v_8 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let (v_10 : expression (bv 32)) <- eval (extract v_4 64 96);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      let (v_12 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let (v_14 : expression (bv 32)) <- eval (extract v_4 128 160);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let (v_16 : expression (bv 32)) <- eval (extract v_4 160 192);
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      let (v_18 : expression (bv 32)) <- eval (extract v_4 192 224);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      let (v_20 : expression (bv 32)) <- eval (extract v_4 224 256);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      let v_22 <- eval (concat (fp_bitcast_to_bv (Float2Half v_19 v_7) 16) (fp_bitcast_to_bv (Float2Half v_21 v_7) 16));
      let v_23 <- eval (concat (fp_bitcast_to_bv (Float2Half v_17 v_7) 16) v_22);
      let v_24 <- eval (concat (fp_bitcast_to_bv (Float2Half v_15 v_7) 16) v_23);
      let v_25 <- eval (concat (fp_bitcast_to_bv (Float2Half v_13 v_7) 16) v_24);
      let v_26 <- eval (concat (fp_bitcast_to_bv (Float2Half v_11 v_7) 16) v_25);
      let v_27 <- eval (concat (fp_bitcast_to_bv (Float2Half v_9 v_7) 16) v_26);
      let v_28 <- eval (concat (fp_bitcast_to_bv (Float2Half v_6 v_7) 16) v_27);
      store v_3 v_28 16;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (ymm_1 : reg (bv 256)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- getRegister (lhs.of_reg ymm_1);
      let (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      let v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      let v_6 <- eval (uvalueMInt (handleImmediateWithSignExtend imm_0 8 8));
      let (v_7 : expression (bv 32)) <- eval (extract v_3 32 64);
      let v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      let (v_9 : expression (bv 32)) <- eval (extract v_3 64 96);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let (v_11 : expression (bv 32)) <- eval (extract v_3 96 128);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let (v_13 : expression (bv 32)) <- eval (extract v_3 128 160);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      let (v_15 : expression (bv 32)) <- eval (extract v_3 160 192);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      let (v_17 : expression (bv 32)) <- eval (extract v_3 192 224);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      let (v_19 : expression (bv 32)) <- eval (extract v_3 224 256);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      let v_21 <- eval (concat (fp_bitcast_to_bv (Float2Half v_18 v_6) 16) (fp_bitcast_to_bv (Float2Half v_20 v_6) 16));
      let v_22 <- eval (concat (fp_bitcast_to_bv (Float2Half v_16 v_6) 16) v_21);
      let v_23 <- eval (concat (fp_bitcast_to_bv (Float2Half v_14 v_6) 16) v_22);
      let v_24 <- eval (concat (fp_bitcast_to_bv (Float2Half v_12 v_6) 16) v_23);
      let v_25 <- eval (concat (fp_bitcast_to_bv (Float2Half v_10 v_6) 16) v_24);
      let v_26 <- eval (concat (fp_bitcast_to_bv (Float2Half v_8 v_6) 16) v_25);
      let v_27 <- eval (concat (fp_bitcast_to_bv (Float2Half v_5 v_6) 16) v_26);
      setRegister (lhs.of_reg xmm_2) v_27;
      pure ()
     action

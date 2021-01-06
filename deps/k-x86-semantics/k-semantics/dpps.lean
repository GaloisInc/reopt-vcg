def dpps : instruction :=
  definst "dpps" $ do
    instr_pat $ fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      let v_7 <- evaluateAddress mem_1;
      let v_8 <- load v_7 16;
      let (v_9 : expression (bv 32)) <- eval (extract v_8 96 128);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      let v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 3) (fp_bitcast_to_bv (fp_mul v_6 v_10) 32) (expression.bv_nat 32 0)));
      let (v_12 : expression (bv 32)) <- eval (extract v_4 64 96);
      let v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      let (v_14 : expression (bv 32)) <- eval (extract v_8 64 96);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 2) (fp_bitcast_to_bv (fp_mul v_13 v_15) 32) (expression.bv_nat 32 0)));
      let v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (fp_bitcast_to_bv (fp_add v_11 v_16) 32));
      let (v_18 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      let (v_20 : expression (bv 32)) <- eval (extract v_8 32 64);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      let v_22 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 1) (fp_bitcast_to_bv (fp_mul v_19 v_21) 32) (expression.bv_nat 32 0)));
      let (v_23 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_24 <- eval (bv_bitcast_to_fp float_class.fp32 v_23);
      let (v_25 : expression (bv 32)) <- eval (extract v_8 0 32);
      let v_26 <- eval (bv_bitcast_to_fp float_class.fp32 v_25);
      let v_27 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 0) (fp_bitcast_to_bv (fp_mul v_24 v_26) 32) (expression.bv_nat 32 0)));
      let v_28 <- eval (bv_bitcast_to_fp float_class.fp32 (fp_bitcast_to_bv (fp_add v_22 v_27) 32));
      let v_29 <- eval (fp_bitcast_to_bv (fp_add v_17 v_28) 32);
      let v_30 <- eval (concat (mux (isBitSet v_3 4) v_29 (expression.bv_nat 32 0)) (mux (isBitSet v_3 5) v_29 (expression.bv_nat 32 0)));
      let v_31 <- eval (concat v_30 (mux (isBitSet v_3 6) v_29 (expression.bv_nat 32 0)));
      let v_32 <- eval (concat v_31 (mux (isBitSet v_3 7) v_29 (expression.bv_nat 32 0)));
      setRegister (lhs.of_reg xmm_2) v_32;
      pure ()
     action;
    instr_pat $ fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) =>
     let action : semantics Unit := do
      let v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      let v_4 <- getRegister (lhs.of_reg xmm_2);
      let (v_5 : expression (bv 32)) <- eval (extract v_4 96 128);
      let v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      let v_7 <- getRegister (lhs.of_reg xmm_1);
      let (v_8 : expression (bv 32)) <- eval (extract v_7 96 128);
      let v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      let v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 3) (fp_bitcast_to_bv (fp_mul v_6 v_9) 32) (expression.bv_nat 32 0)));
      let (v_11 : expression (bv 32)) <- eval (extract v_4 64 96);
      let v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      let (v_13 : expression (bv 32)) <- eval (extract v_7 64 96);
      let v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      let v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 2) (fp_bitcast_to_bv (fp_mul v_12 v_14) 32) (expression.bv_nat 32 0)));
      let v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (fp_bitcast_to_bv (fp_add v_10 v_15) 32));
      let (v_17 : expression (bv 32)) <- eval (extract v_4 32 64);
      let v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      let (v_19 : expression (bv 32)) <- eval (extract v_7 32 64);
      let v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      let v_21 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 1) (fp_bitcast_to_bv (fp_mul v_18 v_20) 32) (expression.bv_nat 32 0)));
      let (v_22 : expression (bv 32)) <- eval (extract v_4 0 32);
      let v_23 <- eval (bv_bitcast_to_fp float_class.fp32 v_22);
      let (v_24 : expression (bv 32)) <- eval (extract v_7 0 32);
      let v_25 <- eval (bv_bitcast_to_fp float_class.fp32 v_24);
      let v_26 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 0) (fp_bitcast_to_bv (fp_mul v_23 v_25) 32) (expression.bv_nat 32 0)));
      let v_27 <- eval (bv_bitcast_to_fp float_class.fp32 (fp_bitcast_to_bv (fp_add v_21 v_26) 32));
      let v_28 <- eval (fp_bitcast_to_bv (fp_add v_16 v_27) 32);
      let v_29 <- eval (concat (mux (isBitSet v_3 4) v_28 (expression.bv_nat 32 0)) (mux (isBitSet v_3 5) v_28 (expression.bv_nat 32 0)));
      let v_30 <- eval (concat v_29 (mux (isBitSet v_3 6) v_28 (expression.bv_nat 32 0)));
      let v_31 <- eval (concat v_30 (mux (isBitSet v_3 7) v_28 (expression.bv_nat 32 0)));
      setRegister (lhs.of_reg xmm_2) v_31;
      pure ()
     action

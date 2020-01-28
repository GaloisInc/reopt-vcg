def dpps : instruction :=
  definst "dpps" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 96 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 3) (fp_bitcast_to_bv (fp_mul v_5 v_8) 32) (expression.bv_nat 32 0)));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 64 96));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 64 96));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 2) (fp_bitcast_to_bv (fp_mul v_10 v_11) 32) (expression.bv_nat 32 0)));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (fp_bitcast_to_bv (fp_add v_9 v_12) 32));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 32 64));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 32 64));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 1) (fp_bitcast_to_bv (fp_mul v_14 v_15) 32) (expression.bv_nat 32 0)));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 0 32));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 0 32));
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 0) (fp_bitcast_to_bv (fp_mul v_17 v_18) 32) (expression.bv_nat 32 0)));
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 (fp_bitcast_to_bv (fp_add v_16 v_19) 32));
      v_21 <- eval (fp_bitcast_to_bv (fp_add v_13 v_20) 32);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (mux (isBitSet v_3 4) v_21 (expression.bv_nat 32 0)) (mux (isBitSet v_3 5) v_21 (expression.bv_nat 32 0))) (mux (isBitSet v_3 6) v_21 (expression.bv_nat 32 0))) (mux (isBitSet v_3 7) v_21 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      v_6 <- getRegister (lhs.of_reg xmm_1);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 96 128));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 3) (fp_bitcast_to_bv (fp_mul v_5 v_7) 32) (expression.bv_nat 32 0)));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 64 96));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 64 96));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 2) (fp_bitcast_to_bv (fp_mul v_9 v_10) 32) (expression.bv_nat 32 0)));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (fp_bitcast_to_bv (fp_add v_8 v_11) 32));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 32 64));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 32 64));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 1) (fp_bitcast_to_bv (fp_mul v_13 v_14) 32) (expression.bv_nat 32 0)));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 0 32));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 0 32));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (mux (isBitSet v_3 0) (fp_bitcast_to_bv (fp_mul v_16 v_17) 32) (expression.bv_nat 32 0)));
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (fp_bitcast_to_bv (fp_add v_15 v_18) 32));
      v_20 <- eval (fp_bitcast_to_bv (fp_add v_12 v_19) 32);
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (mux (isBitSet v_3 4) v_20 (expression.bv_nat 32 0)) (mux (isBitSet v_3 5) v_20 (expression.bv_nat 32 0))) (mux (isBitSet v_3 6) v_20 (expression.bv_nat 32 0))) (mux (isBitSet v_3 7) v_20 (expression.bv_nat 32 0)));
      pure ()
    pat_end

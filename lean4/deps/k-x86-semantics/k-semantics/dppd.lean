def dppd : instruction :=
  definst "dppd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 16;
      (v_9 : expression (bv 64)) <- eval (extract v_8 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_3 3) (fp_bitcast_to_bv (fp_mul v_6 v_10) 64) (expression.bv_nat 64 0)));
      (v_12 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      (v_14 : expression (bv 64)) <- eval (extract v_8 0 64);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 v_14);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_3 2) (fp_bitcast_to_bv (fp_mul v_13 v_15) 64) (expression.bv_nat 64 0)));
      v_17 <- eval (fp_bitcast_to_bv (fp_add v_11 v_16) 64);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_3 6) v_17 (expression.bv_nat 64 0)) (mux (isBitSet v_3 7) v_17 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      (v_5 : expression (bv 64)) <- eval (extract v_4 64 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      v_7 <- getRegister (lhs.of_reg xmm_1);
      (v_8 : expression (bv 64)) <- eval (extract v_7 64 128);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_3 3) (fp_bitcast_to_bv (fp_mul v_6 v_9) 64) (expression.bv_nat 64 0)));
      (v_11 : expression (bv 64)) <- eval (extract v_4 0 64);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      (v_13 : expression (bv 64)) <- eval (extract v_7 0 64);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_3 2) (fp_bitcast_to_bv (fp_mul v_12 v_14) 64) (expression.bv_nat 64 0)));
      v_16 <- eval (fp_bitcast_to_bv (fp_add v_10 v_15) 64);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_3 6) v_16 (expression.bv_nat 64 0)) (mux (isBitSet v_3 7) v_16 (expression.bv_nat 64 0)));
      pure ()
    pat_end

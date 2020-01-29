def vdppd : instruction :=
  definst "vdppd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      v_8 <- evaluateAddress mem_1;
      v_9 <- load v_8 16;
      (v_10 : expression (bv 64)) <- eval (extract v_9 64 128);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_4 3) (fp_bitcast_to_bv (fp_mul v_7 v_11) 64) (expression.bv_nat 64 0)));
      (v_13 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      (v_15 : expression (bv 64)) <- eval (extract v_9 0 64);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 v_15);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_4 2) (fp_bitcast_to_bv (fp_mul v_14 v_16) 64) (expression.bv_nat 64 0)));
      v_18 <- eval (fp_bitcast_to_bv (fp_add v_12 v_17) 64);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 6) v_18 (expression.bv_nat 64 0)) (mux (isBitSet v_4 7) v_18 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      v_8 <- getRegister (lhs.of_reg xmm_1);
      (v_9 : expression (bv 64)) <- eval (extract v_8 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_4 3) (fp_bitcast_to_bv (fp_mul v_7 v_10) 64) (expression.bv_nat 64 0)));
      (v_12 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      (v_14 : expression (bv 64)) <- eval (extract v_8 0 64);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 v_14);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_4 2) (fp_bitcast_to_bv (fp_mul v_13 v_15) 64) (expression.bv_nat 64 0)));
      v_17 <- eval (fp_bitcast_to_bv (fp_add v_11 v_16) 64);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 6) v_17 (expression.bv_nat 64 0)) (mux (isBitSet v_4 7) v_17 (expression.bv_nat 64 0)));
      pure ()
    pat_end

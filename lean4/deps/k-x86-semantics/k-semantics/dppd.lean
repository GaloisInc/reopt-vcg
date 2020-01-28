def dppd : instruction :=
  definst "dppd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 64 128));
      v_6 <- evaluateAddress mem_1;
      v_7 <- load v_6 16;
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 64 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_3 3) (fp_bitcast_to_bv (fp_mul v_5 v_8) 64) (expression.bv_nat 64 0)));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 0 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 0 64));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_3 2) (fp_bitcast_to_bv (fp_mul v_10 v_11) 64) (expression.bv_nat 64 0)));
      v_13 <- eval (fp_bitcast_to_bv (fp_add v_9 v_12) 64);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_3 6) v_13 (expression.bv_nat 64 0)) (mux (isBitSet v_3 7) v_13 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- getRegister (lhs.of_reg xmm_2);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 64 128));
      v_6 <- getRegister (lhs.of_reg xmm_1);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 64 128));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_3 3) (fp_bitcast_to_bv (fp_mul v_5 v_7) 64) (expression.bv_nat 64 0)));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 0 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 0 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_3 2) (fp_bitcast_to_bv (fp_mul v_9 v_10) 64) (expression.bv_nat 64 0)));
      v_12 <- eval (fp_bitcast_to_bv (fp_add v_8 v_11) 64);
      setRegister (lhs.of_reg xmm_2) (concat (mux (isBitSet v_3 6) v_12 (expression.bv_nat 64 0)) (mux (isBitSet v_3 7) v_12 (expression.bv_nat 64 0)));
      pure ()
    pat_end

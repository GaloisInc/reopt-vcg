def vdppd : instruction :=
  definst "vdppd" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 64 128));
      v_7 <- evaluateAddress mem_1;
      v_8 <- load v_7 16;
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_8 64 128));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_4 3) (fp_bitcast_to_bv (fp_mul v_6 v_9) 64) (expression.bv_nat 64 0)));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 0 64));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_8 0 64));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_4 2) (fp_bitcast_to_bv (fp_mul v_11 v_12) 64) (expression.bv_nat 64 0)));
      v_14 <- eval (fp_bitcast_to_bv (fp_add v_10 v_13) 64);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 6) v_14 (expression.bv_nat 64 0)) (mux (isBitSet v_4 7) v_14 (expression.bv_nat 64 0)));
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) (xmm_3 : reg (bv 128)) => do
      v_4 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_5 <- getRegister (lhs.of_reg xmm_2);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 64 128));
      v_7 <- getRegister (lhs.of_reg xmm_1);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 64 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_4 3) (fp_bitcast_to_bv (fp_mul v_6 v_8) 64) (expression.bv_nat 64 0)));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 0 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 0 64));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (mux (isBitSet v_4 2) (fp_bitcast_to_bv (fp_mul v_10 v_11) 64) (expression.bv_nat 64 0)));
      v_13 <- eval (fp_bitcast_to_bv (fp_add v_9 v_12) 64);
      setRegister (lhs.of_reg xmm_3) (concat (mux (isBitSet v_4 6) v_13 (expression.bv_nat 64 0)) (mux (isBitSet v_4 7) v_13 (expression.bv_nat 64 0)));
      pure ()
    pat_end

def vfnmsub231sd : instruction :=
  definst "vfnmsub231sd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_5 96 128);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (concat (expression.bv_nat 32 0) (mux (eq (/- (_,_) -/  mincmp_double (concat (expression.bv_nat 32 0) v_6) (concat (expression.bv_nat 32 0) v_7)) (expression.bv_nat 1 1)) v_6 v_7)));
      (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_8 v_8)) v_10) 64));
      v_12 <- evaluateAddress mem_0;
      v_13 <- load v_12 8;
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      (v_15 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 v_15);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_11 v_14) v_16) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 32)) <- eval (extract v_5 32 64);
      (v_7 : expression (bv 32)) <- eval (extract v_5 96 128);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (concat (expression.bv_nat 32 0) (mux (eq (/- (_,_) -/  mincmp_double (concat (expression.bv_nat 32 0) v_6) (concat (expression.bv_nat 32 0) v_7)) (expression.bv_nat 1 1)) v_6 v_7)));
      (v_9 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_8 v_8)) v_10) 64));
      v_12 <- getRegister (lhs.of_reg xmm_0);
      (v_13 : expression (bv 64)) <- eval (extract v_12 64 128);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      (v_15 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 v_15);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_11 v_14) v_16) 64));
      pure ()
    pat_end

def vfnmsub231sd : instruction :=
  definst "vfnmsub231sd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (extract v_4 32 64);
      v_6 <- eval (extract v_4 96 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 (concat (expression.bv_nat 32 0) (mux (eq (/- (_,_) -/  mincmp_double (concat (expression.bv_nat 32 0) v_5) (concat (expression.bv_nat 32 0) v_6)) (expression.bv_nat 1 1)) v_5 v_6)));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 64 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_7 v_7)) v_8) 64));
      v_10 <- evaluateAddress mem_0;
      v_11 <- load v_10 8;
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_9 v_12) v_13) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (extract v_4 32 64);
      v_6 <- eval (extract v_4 96 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 (concat (expression.bv_nat 32 0) (mux (eq (/- (_,_) -/  mincmp_double (concat (expression.bv_nat 32 0) v_5) (concat (expression.bv_nat 32 0) v_6)) (expression.bv_nat 1 1)) v_5 v_6)));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 64 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_7 v_7)) v_8) 64));
      v_10 <- getRegister (lhs.of_reg xmm_0);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_10 64 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_9 v_11) v_12) 64));
      pure ()
    pat_end

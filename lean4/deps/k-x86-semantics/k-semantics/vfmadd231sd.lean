def vfmadd231sd : instruction :=
  definst "vfmadd231sd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 64 128));
      v_6 <- evaluateAddress mem_0;
      v_7 <- load v_6 8;
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) v_9) 64));
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_8) v_10) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 64 128));
      v_6 <- getRegister (lhs.of_reg xmm_0);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 64 128));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) v_8) 64));
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_7) v_9) 64));
      pure ()
    pat_end

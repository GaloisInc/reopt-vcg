def vfmadd132pd : instruction :=
  definst "vfmadd132pd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- evaluateAddress mem_0;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      v_10 <- getRegister (lhs.of_reg xmm_1);
      (v_11 : expression (bv 64)) <- eval (extract v_10 0 64);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) v_12) 64));
      (v_14 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 v_14);
      (v_16 : expression (bv 64)) <- eval (extract v_7 64 128);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp64 v_16);
      (v_18 : expression (bv 64)) <- eval (extract v_10 64 128);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp64 v_18);
      v_20 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) v_19) 64));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_9) v_13) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_15 v_17) v_20) 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 32;
      (v_9 : expression (bv 64)) <- eval (extract v_8 0 64);
      (v_10 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_11 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_12 : expression (bv 64)) <- eval (extract v_8 64 128);
      (v_13 : expression (bv 64)) <- eval (extract v_3 128 192);
      (v_14 : expression (bv 64)) <- eval (extract v_5 128 192);
      (v_15 : expression (bv 64)) <- eval (extract v_8 128 192);
      (v_16 : expression (bv 64)) <- eval (extract v_3 192 256);
      (v_17 : expression (bv 64)) <- eval (extract v_5 192 256);
      (v_18 : expression (bv 64)) <- eval (extract v_8 192 256);
      setRegister (lhs.of_reg ymm_2) (concat (/- (_,_,_) -/ vfmadd132_double v_4 v_6 v_9) (concat (/- (_,_,_) -/ vfmadd132_double v_10 v_11 v_12) (concat (/- (_,_,_) -/ vfmadd132_double v_13 v_14 v_15) (/- (_,_,_) -/ vfmadd132_double v_16 v_17 v_18))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- getRegister (lhs.of_reg xmm_0);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      v_9 <- getRegister (lhs.of_reg xmm_1);
      (v_10 : expression (bv 64)) <- eval (extract v_9 0 64);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) v_11) 64));
      (v_13 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      (v_15 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 v_15);
      (v_17 : expression (bv 64)) <- eval (extract v_9 64 128);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp64 v_17);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp64 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul (MInt2Float (expression.bv_nat 64 0) 53 11) (MInt2Float (expression.bv_nat 64 0) 53 11))) v_18) 64));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_5 v_8) v_12) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_14 v_16) v_19) 64));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 0 64);
      v_7 <- getRegister (lhs.of_reg ymm_0);
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      (v_10 : expression (bv 64)) <- eval (extract v_5 64 128);
      (v_11 : expression (bv 64)) <- eval (extract v_7 64 128);
      (v_12 : expression (bv 64)) <- eval (extract v_3 128 192);
      (v_13 : expression (bv 64)) <- eval (extract v_5 128 192);
      (v_14 : expression (bv 64)) <- eval (extract v_7 128 192);
      (v_15 : expression (bv 64)) <- eval (extract v_3 192 256);
      (v_16 : expression (bv 64)) <- eval (extract v_5 192 256);
      (v_17 : expression (bv 64)) <- eval (extract v_7 192 256);
      setRegister (lhs.of_reg ymm_2) (concat (/- (_,_,_) -/ vfmadd132_double v_4 v_6 v_8) (concat (/- (_,_,_) -/ vfmadd132_double v_9 v_10 v_11) (concat (/- (_,_,_) -/ vfmadd132_double v_12 v_13 v_14) (/- (_,_,_) -/ vfmadd132_double v_15 v_16 v_17))));
      pure ()
    pat_end

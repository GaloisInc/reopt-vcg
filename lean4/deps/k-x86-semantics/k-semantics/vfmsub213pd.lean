def vfmsub213pd : instruction :=
  definst "vfmsub213pd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 0 64));
      v_5 <- getRegister (lhs.of_reg xmm_2);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 0 64));
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 16;
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_8 0 64));
      v_10 <- eval (fp_bitcast_to_bv (fp_sub (fp_mul v_4 v_6) v_9) 64);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 64 128));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_8 64 128));
      setRegister (lhs.of_reg xmm_2) (concat (concat (extract v_10 0 56) (extract v_10 56 64)) (fp_bitcast_to_bv (fp_sub (fp_mul v_11 v_12) v_13) 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 0 64));
      v_5 <- getRegister (lhs.of_reg ymm_2);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 0 64));
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 32;
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_8 0 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 64 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_8 64 128));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 128 192));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 128 192));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_8 128 192));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 192 256));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 192 256));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_8 192 256));
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_4 v_6) v_9) 64) (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_10 v_11) v_12) 64) (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_13 v_14) v_15) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_16 v_17) v_18) 64))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 0 64));
      v_5 <- getRegister (lhs.of_reg xmm_2);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 0 64));
      v_7 <- getRegister (lhs.of_reg xmm_0);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 0 64));
      v_9 <- eval (fp_bitcast_to_bv (fp_sub (fp_mul v_4 v_6) v_8) 64);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 64 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 64 128));
      setRegister (lhs.of_reg xmm_2) (concat (concat (extract v_9 0 56) (extract v_9 56 64)) (fp_bitcast_to_bv (fp_sub (fp_mul v_10 v_11) v_12) 64));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 0 64));
      v_5 <- getRegister (lhs.of_reg ymm_2);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 0 64));
      v_7 <- getRegister (lhs.of_reg ymm_0);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 0 64));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 64 128));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 64 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 128 192));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 128 192));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 128 192));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 192 256));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_5 192 256));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 192 256));
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_4 v_6) v_8) 64) (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_9 v_10) v_11) 64) (concat (fp_bitcast_to_bv (fp_sub (fp_mul v_12 v_13) v_14) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_15 v_16) v_17) 64))));
      pure ()
    pat_end

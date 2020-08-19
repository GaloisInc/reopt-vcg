def vfmaddsub213pd : instruction :=
  definst "vfmaddsub213pd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- getRegister (lhs.of_reg xmm_2);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      v_9 <- evaluateAddress mem_0;
      v_10 <- load v_9 16;
      (v_11 : expression (bv 64)) <- eval (extract v_10 0 64);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      (v_13 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      (v_15 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 v_15);
      (v_17 : expression (bv 64)) <- eval (extract v_10 64 128);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp64 v_17);
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_add (fp_mul v_5 v_8) v_12) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_14 v_16) v_18) 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- getRegister (lhs.of_reg ymm_2);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      v_9 <- evaluateAddress mem_0;
      v_10 <- load v_9 32;
      (v_11 : expression (bv 64)) <- eval (extract v_10 0 64);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      (v_13 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      (v_15 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 v_15);
      (v_17 : expression (bv 64)) <- eval (extract v_10 64 128);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp64 v_17);
      (v_19 : expression (bv 64)) <- eval (extract v_3 128 192);
      v_20 <- eval (bv_bitcast_to_fp float_class.fp64 v_19);
      (v_21 : expression (bv 64)) <- eval (extract v_6 128 192);
      v_22 <- eval (bv_bitcast_to_fp float_class.fp64 v_21);
      (v_23 : expression (bv 64)) <- eval (extract v_10 128 192);
      v_24 <- eval (bv_bitcast_to_fp float_class.fp64 v_23);
      (v_25 : expression (bv 64)) <- eval (extract v_3 192 256);
      v_26 <- eval (bv_bitcast_to_fp float_class.fp64 v_25);
      (v_27 : expression (bv 64)) <- eval (extract v_6 192 256);
      v_28 <- eval (bv_bitcast_to_fp float_class.fp64 v_27);
      (v_29 : expression (bv 64)) <- eval (extract v_10 192 256);
      v_30 <- eval (bv_bitcast_to_fp float_class.fp64 v_29);
      setRegister (lhs.of_reg ymm_2) (concat (concat (fp_bitcast_to_bv (fp_add (fp_mul v_5 v_8) v_12) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_14 v_16) v_18) 64)) (concat (fp_bitcast_to_bv (fp_add (fp_mul v_20 v_22) v_24) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_26 v_28) v_30) 64)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- getRegister (lhs.of_reg xmm_2);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      v_9 <- getRegister (lhs.of_reg xmm_0);
      (v_10 : expression (bv 64)) <- eval (extract v_9 0 64);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      (v_12 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      (v_14 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 v_14);
      (v_16 : expression (bv 64)) <- eval (extract v_9 64 128);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp64 v_16);
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_add (fp_mul v_5 v_8) v_11) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_13 v_15) v_17) 64));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- getRegister (lhs.of_reg ymm_2);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      v_9 <- getRegister (lhs.of_reg ymm_0);
      (v_10 : expression (bv 64)) <- eval (extract v_9 0 64);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      (v_12 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      (v_14 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 v_14);
      (v_16 : expression (bv 64)) <- eval (extract v_9 64 128);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp64 v_16);
      (v_18 : expression (bv 64)) <- eval (extract v_3 128 192);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp64 v_18);
      (v_20 : expression (bv 64)) <- eval (extract v_6 128 192);
      v_21 <- eval (bv_bitcast_to_fp float_class.fp64 v_20);
      (v_22 : expression (bv 64)) <- eval (extract v_9 128 192);
      v_23 <- eval (bv_bitcast_to_fp float_class.fp64 v_22);
      (v_24 : expression (bv 64)) <- eval (extract v_3 192 256);
      v_25 <- eval (bv_bitcast_to_fp float_class.fp64 v_24);
      (v_26 : expression (bv 64)) <- eval (extract v_6 192 256);
      v_27 <- eval (bv_bitcast_to_fp float_class.fp64 v_26);
      (v_28 : expression (bv 64)) <- eval (extract v_9 192 256);
      v_29 <- eval (bv_bitcast_to_fp float_class.fp64 v_28);
      setRegister (lhs.of_reg ymm_2) (concat (concat (fp_bitcast_to_bv (fp_add (fp_mul v_5 v_8) v_11) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_13 v_15) v_17) 64)) (concat (fp_bitcast_to_bv (fp_add (fp_mul v_19 v_21) v_23) 64) (fp_bitcast_to_bv (fp_sub (fp_mul v_25 v_27) v_29) 64)));
      pure ()
    pat_end
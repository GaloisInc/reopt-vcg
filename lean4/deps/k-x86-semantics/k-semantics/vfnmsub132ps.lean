def vfnmsub132ps : instruction :=
  definst "vfnmsub132ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 0 32));
      v_8 <- getRegister (lhs.of_reg xmm_1);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 0 32));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 32 64));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 32 64));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 64 96));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 64 96));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 96 128));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 96 128));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_4 v_7)) v_9) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_10 v_11)) v_12) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_13 v_14)) v_15) 32) (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_16 v_17)) v_18) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 0 32));
      v_8 <- getRegister (lhs.of_reg ymm_1);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 0 32));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 32 64));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 32 64));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 64 96));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 64 96));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 96 128));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 96 128));
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 128 160));
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 128 160));
      v_21 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 128 160));
      v_22 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 160 192));
      v_23 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 160 192));
      v_24 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 160 192));
      v_25 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 192 224));
      v_26 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 192 224));
      v_27 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 192 224));
      v_28 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 224 256));
      v_29 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 224 256));
      v_30 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 224 256));
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_4 v_7)) v_9) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_10 v_11)) v_12) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_13 v_14)) v_15) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_16 v_17)) v_18) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_19 v_20)) v_21) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_22 v_23)) v_24) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_25 v_26)) v_27) 32) (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_28 v_29)) v_30) 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- getRegister (lhs.of_reg xmm_0);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 0 32));
      v_7 <- getRegister (lhs.of_reg xmm_1);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 0 32));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 32 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 32 64));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 64 96));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 64 96));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 96 128));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 96 128));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_4 v_6)) v_8) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_9 v_10)) v_11) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_12 v_13)) v_14) 32) (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_15 v_16)) v_17) 32))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- getRegister (lhs.of_reg ymm_0);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 0 32));
      v_7 <- getRegister (lhs.of_reg ymm_1);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 0 32));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 32 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 32 64));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 64 96));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 64 96));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 96 128));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 96 128));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 128 160));
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 128 160));
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 128 160));
      v_21 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 160 192));
      v_22 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 160 192));
      v_23 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 160 192));
      v_24 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 192 224));
      v_25 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 192 224));
      v_26 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 192 224));
      v_27 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 224 256));
      v_28 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 224 256));
      v_29 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_7 224 256));
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_4 v_6)) v_8) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_9 v_10)) v_11) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_12 v_13)) v_14) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_15 v_16)) v_17) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_18 v_19)) v_20) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_21 v_22)) v_23) 32) (concat (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_24 v_25)) v_26) 32) (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_27 v_28)) v_29) 32))))))));
      pure ()
    pat_end

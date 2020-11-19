def vrsqrtps : instruction :=
  definst "vrsqrtps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_4));
      (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_6));
      (v_8 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_8));
      (v_10 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_10));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_5) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_7) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_9) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_11) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_4));
      (v_6 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_6));
      (v_8 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_8));
      (v_10 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_10));
      (v_12 : expression (bv 32)) <- eval (extract v_3 128 160);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_12));
      (v_14 : expression (bv 32)) <- eval (extract v_3 160 192);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_14));
      (v_16 : expression (bv 32)) <- eval (extract v_3 192 224);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_16));
      (v_18 : expression (bv 32)) <- eval (extract v_3 224 256);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_18));
      setRegister (lhs.of_reg ymm_1) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_5) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_7) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_9) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_11) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_13) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_15) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_17) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_19) 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_3));
      (v_5 : expression (bv 32)) <- eval (extract v_2 32 64);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_2 64 96);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_7));
      (v_9 : expression (bv 32)) <- eval (extract v_2 96 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_9));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_4) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_6) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_8) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_10) 32))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_3));
      (v_5 : expression (bv 32)) <- eval (extract v_2 32 64);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_5));
      (v_7 : expression (bv 32)) <- eval (extract v_2 64 96);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_7));
      (v_9 : expression (bv 32)) <- eval (extract v_2 96 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_9));
      (v_11 : expression (bv 32)) <- eval (extract v_2 128 160);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_11));
      (v_13 : expression (bv 32)) <- eval (extract v_2 160 192);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_13));
      (v_15 : expression (bv 32)) <- eval (extract v_2 192 224);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_15));
      (v_17 : expression (bv 32)) <- eval (extract v_2 224 256);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_17));
      setRegister (lhs.of_reg ymm_1) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_4) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_6) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_8) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_10) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_12) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_14) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_16) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_18) 32))))))));
      pure ()
    pat_end

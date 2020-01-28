def vdivps : instruction :=
  definst "vdivps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 16;
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 0 32));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 32 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 64 96));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 96 128));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_div v_4 v_7) 32) (concat (fp_bitcast_to_bv (fp_div v_8 v_9) 32) (concat (fp_bitcast_to_bv (fp_div v_10 v_11) 32) (fp_bitcast_to_bv (fp_div v_12 v_13) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 32;
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 0 32));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 32 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 64 96));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 96 128));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 128 160));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 128 160));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 160 192));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 160 192));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 192 224));
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 192 224));
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 224 256));
      v_21 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_6 224 256));
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_div v_4 v_7) 32) (concat (fp_bitcast_to_bv (fp_div v_8 v_9) 32) (concat (fp_bitcast_to_bv (fp_div v_10 v_11) 32) (concat (fp_bitcast_to_bv (fp_div v_12 v_13) 32) (concat (fp_bitcast_to_bv (fp_div v_14 v_15) 32) (concat (fp_bitcast_to_bv (fp_div v_16 v_17) 32) (concat (fp_bitcast_to_bv (fp_div v_18 v_19) 32) (fp_bitcast_to_bv (fp_div v_20 v_21) 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- getRegister (lhs.of_reg xmm_0);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 0 32));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 32 64));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 64 96));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 96 128));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_div v_4 v_6) 32) (concat (fp_bitcast_to_bv (fp_div v_7 v_8) 32) (concat (fp_bitcast_to_bv (fp_div v_9 v_10) 32) (fp_bitcast_to_bv (fp_div v_11 v_12) 32))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- getRegister (lhs.of_reg ymm_0);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 0 32));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 32 64));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 64 96));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 96 128));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 128 160));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 128 160));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 160 192));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 160 192));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 192 224));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 192 224));
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 224 256));
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_5 224 256));
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_div v_4 v_6) 32) (concat (fp_bitcast_to_bv (fp_div v_7 v_8) 32) (concat (fp_bitcast_to_bv (fp_div v_9 v_10) 32) (concat (fp_bitcast_to_bv (fp_div v_11 v_12) 32) (concat (fp_bitcast_to_bv (fp_div v_13 v_14) 32) (concat (fp_bitcast_to_bv (fp_div v_15 v_16) 32) (concat (fp_bitcast_to_bv (fp_div v_17 v_18) 32) (fp_bitcast_to_bv (fp_div v_19 v_20) 32))))))));
      pure ()
    pat_end

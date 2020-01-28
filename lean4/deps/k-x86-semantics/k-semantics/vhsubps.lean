def vhsubps : instruction :=
  definst "vhsubps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 32 64));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 0 32));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 64 96));
      v_9 <- getRegister (lhs.of_reg xmm_1);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 32 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 0 32));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 96 128));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 64 96));
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (fp_bitcast_to_bv (fp_sub v_5 v_6) 32) (fp_bitcast_to_bv (fp_sub v_7 v_8) 32)) (fp_bitcast_to_bv (fp_sub v_10 v_11) 32)) (fp_bitcast_to_bv (fp_sub v_12 v_13) 32));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 32 64));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 0 32));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 96 128));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 64 96));
      v_9 <- getRegister (lhs.of_reg ymm_1);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 32 64));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 0 32));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 96 128));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 64 96));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 160 192));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 128 160));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 224 256));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_4 192 224));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 160 192));
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 128 160));
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 224 256));
      v_21 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_9 192 224));
      setRegister (lhs.of_reg ymm_2) (concat (concat (concat (concat (fp_bitcast_to_bv (fp_sub v_5 v_6) 32) (fp_bitcast_to_bv (fp_sub v_7 v_8) 32)) (fp_bitcast_to_bv (fp_sub v_10 v_11) 32)) (fp_bitcast_to_bv (fp_sub v_12 v_13) 32)) (concat (concat (concat (fp_bitcast_to_bv (fp_sub v_14 v_15) 32) (fp_bitcast_to_bv (fp_sub v_16 v_17) 32)) (fp_bitcast_to_bv (fp_sub v_18 v_19) 32)) (fp_bitcast_to_bv (fp_sub v_20 v_21) 32)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_8 <- getRegister (lhs.of_reg xmm_1);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 32 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 0 32));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 96 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 64 96));
      setRegister (lhs.of_reg xmm_2) (concat (concat (concat (fp_bitcast_to_bv (fp_sub v_4 v_5) 32) (fp_bitcast_to_bv (fp_sub v_6 v_7) 32)) (fp_bitcast_to_bv (fp_sub v_9 v_10) 32)) (fp_bitcast_to_bv (fp_sub v_11 v_12) 32));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_8 <- getRegister (lhs.of_reg ymm_1);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 32 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 0 32));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 96 128));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 64 96));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 160 192));
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 128 160));
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 224 256));
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 192 224));
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 160 192));
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 128 160));
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 224 256));
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_8 192 224));
      setRegister (lhs.of_reg ymm_2) (concat (concat (concat (concat (fp_bitcast_to_bv (fp_sub v_4 v_5) 32) (fp_bitcast_to_bv (fp_sub v_6 v_7) 32)) (fp_bitcast_to_bv (fp_sub v_9 v_10) 32)) (fp_bitcast_to_bv (fp_sub v_11 v_12) 32)) (concat (concat (concat (fp_bitcast_to_bv (fp_sub v_13 v_14) 32) (fp_bitcast_to_bv (fp_sub v_15 v_16) 32)) (fp_bitcast_to_bv (fp_sub v_17 v_18) 32)) (fp_bitcast_to_bv (fp_sub v_19 v_20) 32)));
      pure ()
    pat_end

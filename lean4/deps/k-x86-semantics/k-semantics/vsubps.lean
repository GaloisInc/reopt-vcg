def vsubps : instruction :=
  definst "vsubps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      v_6 <- evaluateAddress mem_0;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      (v_12 : expression (bv 32)) <- eval (extract v_7 32 64);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      (v_14 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      (v_16 : expression (bv 32)) <- eval (extract v_7 64 96);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      (v_18 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      (v_20 : expression (bv 32)) <- eval (extract v_7 96 128);
      v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_sub v_5 v_9) 32) (concat (fp_bitcast_to_bv (fp_sub v_11 v_13) 32) (concat (fp_bitcast_to_bv (fp_sub v_15 v_17) 32) (fp_bitcast_to_bv (fp_sub v_19 v_21) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      v_6 <- evaluateAddress mem_0;
      v_7 <- load v_6 32;
      (v_8 : expression (bv 32)) <- eval (extract v_7 0 32);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      (v_10 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp32 v_10);
      (v_12 : expression (bv 32)) <- eval (extract v_7 32 64);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp32 v_12);
      (v_14 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp32 v_14);
      (v_16 : expression (bv 32)) <- eval (extract v_7 64 96);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp32 v_16);
      (v_18 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp32 v_18);
      (v_20 : expression (bv 32)) <- eval (extract v_7 96 128);
      v_21 <- eval (bv_bitcast_to_fp float_class.fp32 v_20);
      (v_22 : expression (bv 32)) <- eval (extract v_3 128 160);
      v_23 <- eval (bv_bitcast_to_fp float_class.fp32 v_22);
      (v_24 : expression (bv 32)) <- eval (extract v_7 128 160);
      v_25 <- eval (bv_bitcast_to_fp float_class.fp32 v_24);
      (v_26 : expression (bv 32)) <- eval (extract v_3 160 192);
      v_27 <- eval (bv_bitcast_to_fp float_class.fp32 v_26);
      (v_28 : expression (bv 32)) <- eval (extract v_7 160 192);
      v_29 <- eval (bv_bitcast_to_fp float_class.fp32 v_28);
      (v_30 : expression (bv 32)) <- eval (extract v_3 192 224);
      v_31 <- eval (bv_bitcast_to_fp float_class.fp32 v_30);
      (v_32 : expression (bv 32)) <- eval (extract v_7 192 224);
      v_33 <- eval (bv_bitcast_to_fp float_class.fp32 v_32);
      (v_34 : expression (bv 32)) <- eval (extract v_3 224 256);
      v_35 <- eval (bv_bitcast_to_fp float_class.fp32 v_34);
      (v_36 : expression (bv 32)) <- eval (extract v_7 224 256);
      v_37 <- eval (bv_bitcast_to_fp float_class.fp32 v_36);
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_sub v_5 v_9) 32) (concat (fp_bitcast_to_bv (fp_sub v_11 v_13) 32) (concat (fp_bitcast_to_bv (fp_sub v_15 v_17) 32) (concat (fp_bitcast_to_bv (fp_sub v_19 v_21) 32) (concat (fp_bitcast_to_bv (fp_sub v_23 v_25) 32) (concat (fp_bitcast_to_bv (fp_sub v_27 v_29) 32) (concat (fp_bitcast_to_bv (fp_sub v_31 v_33) 32) (fp_bitcast_to_bv (fp_sub v_35 v_37) 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      v_6 <- getRegister (lhs.of_reg xmm_0);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      (v_11 : expression (bv 32)) <- eval (extract v_6 32 64);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      (v_13 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      (v_15 : expression (bv 32)) <- eval (extract v_6 64 96);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      (v_17 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      (v_19 : expression (bv 32)) <- eval (extract v_6 96 128);
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_sub v_5 v_8) 32) (concat (fp_bitcast_to_bv (fp_sub v_10 v_12) 32) (concat (fp_bitcast_to_bv (fp_sub v_14 v_16) 32) (fp_bitcast_to_bv (fp_sub v_18 v_20) 32))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 v_4);
      v_6 <- getRegister (lhs.of_reg ymm_0);
      (v_7 : expression (bv 32)) <- eval (extract v_6 0 32);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp32 v_7);
      (v_9 : expression (bv 32)) <- eval (extract v_3 32 64);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp32 v_9);
      (v_11 : expression (bv 32)) <- eval (extract v_6 32 64);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      (v_13 : expression (bv 32)) <- eval (extract v_3 64 96);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp32 v_13);
      (v_15 : expression (bv 32)) <- eval (extract v_6 64 96);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp32 v_15);
      (v_17 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp32 v_17);
      (v_19 : expression (bv 32)) <- eval (extract v_6 96 128);
      v_20 <- eval (bv_bitcast_to_fp float_class.fp32 v_19);
      (v_21 : expression (bv 32)) <- eval (extract v_3 128 160);
      v_22 <- eval (bv_bitcast_to_fp float_class.fp32 v_21);
      (v_23 : expression (bv 32)) <- eval (extract v_6 128 160);
      v_24 <- eval (bv_bitcast_to_fp float_class.fp32 v_23);
      (v_25 : expression (bv 32)) <- eval (extract v_3 160 192);
      v_26 <- eval (bv_bitcast_to_fp float_class.fp32 v_25);
      (v_27 : expression (bv 32)) <- eval (extract v_6 160 192);
      v_28 <- eval (bv_bitcast_to_fp float_class.fp32 v_27);
      (v_29 : expression (bv 32)) <- eval (extract v_3 192 224);
      v_30 <- eval (bv_bitcast_to_fp float_class.fp32 v_29);
      (v_31 : expression (bv 32)) <- eval (extract v_6 192 224);
      v_32 <- eval (bv_bitcast_to_fp float_class.fp32 v_31);
      (v_33 : expression (bv 32)) <- eval (extract v_3 224 256);
      v_34 <- eval (bv_bitcast_to_fp float_class.fp32 v_33);
      (v_35 : expression (bv 32)) <- eval (extract v_6 224 256);
      v_36 <- eval (bv_bitcast_to_fp float_class.fp32 v_35);
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_sub v_5 v_8) 32) (concat (fp_bitcast_to_bv (fp_sub v_10 v_12) 32) (concat (fp_bitcast_to_bv (fp_sub v_14 v_16) 32) (concat (fp_bitcast_to_bv (fp_sub v_18 v_20) 32) (concat (fp_bitcast_to_bv (fp_sub v_22 v_24) 32) (concat (fp_bitcast_to_bv (fp_sub v_26 v_28) 32) (concat (fp_bitcast_to_bv (fp_sub v_30 v_32) 32) (fp_bitcast_to_bv (fp_sub v_34 v_36) 32))))))));
      pure ()
    pat_end

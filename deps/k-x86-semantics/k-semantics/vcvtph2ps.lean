def vcvtph2ps : instruction :=
  definst "vcvtph2ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp16 v_4);
      (v_6 : expression (bv 16)) <- eval (extract v_3 16 32);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp16 v_6);
      (v_8 : expression (bv 16)) <- eval (extract v_3 32 48);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp16 v_8);
      (v_10 : expression (bv 16)) <- eval (extract v_3 48 64);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp16 v_10);
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_7 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_9 24 8) 32) (fp_bitcast_to_bv (fp_round v_11 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 16)) <- eval (extract v_3 0 16);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp16 v_4);
      (v_6 : expression (bv 16)) <- eval (extract v_3 16 32);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp16 v_6);
      (v_8 : expression (bv 16)) <- eval (extract v_3 32 48);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp16 v_8);
      (v_10 : expression (bv 16)) <- eval (extract v_3 48 64);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp16 v_10);
      (v_12 : expression (bv 16)) <- eval (extract v_3 64 80);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp16 v_12);
      (v_14 : expression (bv 16)) <- eval (extract v_3 80 96);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp16 v_14);
      (v_16 : expression (bv 16)) <- eval (extract v_3 96 112);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp16 v_16);
      (v_18 : expression (bv 16)) <- eval (extract v_3 112 128);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp16 v_18);
      setRegister (lhs.of_reg ymm_1) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_7 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_9 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_11 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_13 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_15 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_17 24 8) 32) (fp_bitcast_to_bv (fp_round v_19 24 8) 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 64 80);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp16 v_3);
      (v_5 : expression (bv 16)) <- eval (extract v_2 80 96);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp16 v_5);
      (v_7 : expression (bv 16)) <- eval (extract v_2 96 112);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp16 v_7);
      (v_9 : expression (bv 16)) <- eval (extract v_2 112 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp16 v_9);
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_6 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_8 24 8) 32) (fp_bitcast_to_bv (fp_round v_10 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (ymm_1 : reg (bv 256)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 16)) <- eval (extract v_2 0 16);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp16 v_3);
      (v_5 : expression (bv 16)) <- eval (extract v_2 16 32);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp16 v_5);
      (v_7 : expression (bv 16)) <- eval (extract v_2 32 48);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp16 v_7);
      (v_9 : expression (bv 16)) <- eval (extract v_2 48 64);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp16 v_9);
      (v_11 : expression (bv 16)) <- eval (extract v_2 64 80);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp16 v_11);
      (v_13 : expression (bv 16)) <- eval (extract v_2 80 96);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp16 v_13);
      (v_15 : expression (bv 16)) <- eval (extract v_2 96 112);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp16 v_15);
      (v_17 : expression (bv 16)) <- eval (extract v_2 112 128);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp16 v_17);
      setRegister (lhs.of_reg ymm_1) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_6 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_8 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_10 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_12 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_14 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_16 24 8) 32) (fp_bitcast_to_bv (fp_round v_18 24 8) 32))))))));
      pure ()
    pat_end

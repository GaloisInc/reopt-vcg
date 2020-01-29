def vaddpd : instruction :=
  definst "vaddpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- evaluateAddress mem_0;
      v_7 <- load v_6 16;
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      (v_10 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      (v_12 : expression (bv 64)) <- eval (extract v_7 64 128);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_add v_5 v_9) 64) (fp_bitcast_to_bv (fp_add v_11 v_13) 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- evaluateAddress mem_0;
      v_7 <- load v_6 32;
      (v_8 : expression (bv 64)) <- eval (extract v_7 0 64);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      (v_10 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      (v_12 : expression (bv 64)) <- eval (extract v_7 64 128);
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 v_12);
      (v_14 : expression (bv 64)) <- eval (extract v_3 128 192);
      v_15 <- eval (bv_bitcast_to_fp float_class.fp64 v_14);
      (v_16 : expression (bv 64)) <- eval (extract v_7 128 192);
      v_17 <- eval (bv_bitcast_to_fp float_class.fp64 v_16);
      (v_18 : expression (bv 64)) <- eval (extract v_3 192 256);
      v_19 <- eval (bv_bitcast_to_fp float_class.fp64 v_18);
      (v_20 : expression (bv 64)) <- eval (extract v_7 192 256);
      v_21 <- eval (bv_bitcast_to_fp float_class.fp64 v_20);
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_add v_5 v_9) 64) (concat (fp_bitcast_to_bv (fp_add v_11 v_13) 64) (concat (fp_bitcast_to_bv (fp_add v_15 v_17) 64) (fp_bitcast_to_bv (fp_add v_19 v_21) 64))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- getRegister (lhs.of_reg xmm_0);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      (v_11 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_add v_5 v_8) 64) (fp_bitcast_to_bv (fp_add v_10 v_12) 64));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_1);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      v_6 <- getRegister (lhs.of_reg ymm_0);
      (v_7 : expression (bv 64)) <- eval (extract v_6 0 64);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      (v_9 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      (v_11 : expression (bv 64)) <- eval (extract v_6 64 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      (v_13 : expression (bv 64)) <- eval (extract v_3 128 192);
      v_14 <- eval (bv_bitcast_to_fp float_class.fp64 v_13);
      (v_15 : expression (bv 64)) <- eval (extract v_6 128 192);
      v_16 <- eval (bv_bitcast_to_fp float_class.fp64 v_15);
      (v_17 : expression (bv 64)) <- eval (extract v_3 192 256);
      v_18 <- eval (bv_bitcast_to_fp float_class.fp64 v_17);
      (v_19 : expression (bv 64)) <- eval (extract v_6 192 256);
      v_20 <- eval (bv_bitcast_to_fp float_class.fp64 v_19);
      setRegister (lhs.of_reg ymm_2) (concat (fp_bitcast_to_bv (fp_add v_5 v_8) 64) (concat (fp_bitcast_to_bv (fp_add v_10 v_12) 64) (concat (fp_bitcast_to_bv (fp_add v_14 v_16) 64) (fp_bitcast_to_bv (fp_add v_18 v_20) 64))));
      pure ()
    pat_end

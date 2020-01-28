def vhsubpd : instruction :=
  definst "vhsubpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 64 128));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 0 64));
      v_7 <- getRegister (lhs.of_reg xmm_1);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 64 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 0 64));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_sub v_5 v_6) 64) (fp_bitcast_to_bv (fp_sub v_8 v_9) 64));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 32;
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 64 128));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 0 64));
      v_7 <- getRegister (lhs.of_reg ymm_1);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 64 128));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 0 64));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 192 256));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_4 128 192));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 192 256));
      v_13 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_7 128 192));
      setRegister (lhs.of_reg ymm_2) (concat (concat (fp_bitcast_to_bv (fp_sub v_5 v_6) 64) (fp_bitcast_to_bv (fp_sub v_8 v_9) 64)) (concat (fp_bitcast_to_bv (fp_sub v_10 v_11) 64) (fp_bitcast_to_bv (fp_sub v_12 v_13) 64)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 0 64));
      v_6 <- getRegister (lhs.of_reg xmm_1);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 64 128));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 0 64));
      setRegister (lhs.of_reg xmm_2) (concat (fp_bitcast_to_bv (fp_sub v_4 v_5) 64) (fp_bitcast_to_bv (fp_sub v_7 v_8) 64));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_0);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 0 64));
      v_6 <- getRegister (lhs.of_reg ymm_1);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 64 128));
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 0 64));
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 192 256));
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 128 192));
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 192 256));
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_6 128 192));
      setRegister (lhs.of_reg ymm_2) (concat (concat (fp_bitcast_to_bv (fp_sub v_4 v_5) 64) (fp_bitcast_to_bv (fp_sub v_7 v_8) 64)) (concat (fp_bitcast_to_bv (fp_sub v_9 v_10) 64) (fp_bitcast_to_bv (fp_sub v_11 v_12) 64)));
      pure ()
    pat_end

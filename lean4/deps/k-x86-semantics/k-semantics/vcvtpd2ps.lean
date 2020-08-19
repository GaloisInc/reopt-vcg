def vcvtpd2ps : instruction :=
  definst "vcvtpd2ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      (v_6 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      (v_8 : expression (bv 64)) <- eval (extract v_3 128 192);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      (v_10 : expression (bv 64)) <- eval (extract v_3 192 256);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_7 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_9 24 8) 32) (fp_bitcast_to_bv (fp_round v_11 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      (v_6 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (fp_bitcast_to_bv (fp_round v_7 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      (v_6 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      (v_8 : expression (bv 64)) <- eval (extract v_3 128 192);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      (v_10 : expression (bv 64)) <- eval (extract v_3 192 256);
      v_11 <- eval (bv_bitcast_to_fp float_class.fp64 v_10);
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_7 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_9 24 8) 32) (fp_bitcast_to_bv (fp_round v_11 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 v_4);
      (v_6 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (fp_bitcast_to_bv (fp_round v_5 24 8) 32) (fp_bitcast_to_bv (fp_round v_7 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 v_3);
      (v_5 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (fp_bitcast_to_bv (fp_round v_6 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 v_3);
      (v_5 : expression (bv 64)) <- eval (extract v_2 64 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp64 v_5);
      (v_7 : expression (bv 64)) <- eval (extract v_2 128 192);
      v_8 <- eval (bv_bitcast_to_fp float_class.fp64 v_7);
      (v_9 : expression (bv 64)) <- eval (extract v_2 192 256);
      v_10 <- eval (bv_bitcast_to_fp float_class.fp64 v_9);
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_6 24 8) 32) (concat (fp_bitcast_to_bv (fp_round v_8 24 8) 32) (fp_bitcast_to_bv (fp_round v_10 24 8) 32))));
      pure ()
    pat_end
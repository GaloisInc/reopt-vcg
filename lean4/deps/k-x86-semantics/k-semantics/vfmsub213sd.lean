def vfmsub213sd : instruction :=
  definst "vfmsub213sd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      v_10 <- evaluateAddress mem_0;
      v_11 <- load v_10 8;
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_7 v_9) v_12) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      (v_6 : expression (bv 64)) <- eval (extract v_5 64 128);
      v_7 <- eval (bv_bitcast_to_fp float_class.fp64 v_6);
      (v_8 : expression (bv 64)) <- eval (extract v_3 64 128);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp64 v_8);
      v_10 <- getRegister (lhs.of_reg xmm_0);
      (v_11 : expression (bv 64)) <- eval (extract v_10 64 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp64 v_11);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul v_7 v_9) v_12) 64));
      pure ()
    pat_end
def vfnmsub132ss : instruction :=
  definst "vfnmsub132ss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      v_7 <- evaluateAddress mem_0;
      v_8 <- load v_7 4;
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      v_10 <- getRegister (lhs.of_reg xmm_1);
      (v_11 : expression (bv 32)) <- eval (extract v_10 96 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_6 v_9)) v_12) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      (v_4 : expression (bv 96)) <- eval (extract v_3 0 96);
      (v_5 : expression (bv 32)) <- eval (extract v_3 96 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      v_7 <- getRegister (lhs.of_reg xmm_0);
      (v_8 : expression (bv 32)) <- eval (extract v_7 96 128);
      v_9 <- eval (bv_bitcast_to_fp float_class.fp32 v_8);
      v_10 <- getRegister (lhs.of_reg xmm_1);
      (v_11 : expression (bv 32)) <- eval (extract v_10 96 128);
      v_12 <- eval (bv_bitcast_to_fp float_class.fp32 v_11);
      setRegister (lhs.of_reg xmm_2) (concat v_4 (fp_bitcast_to_bv (fp_sub (fp_mul -1e+00 (fp_mul v_6 v_9)) v_12) 32));
      pure ()
    pat_end

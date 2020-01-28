def rcpps : instruction :=
  definst "rcpps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 0 32));
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 32 64));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 64 96));
      v_7 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_3 96 128));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_4) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_5) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_6) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_7) 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      v_3 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 0 32));
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 32 64));
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 64 96));
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 (extract v_2 96 128));
      setRegister (lhs.of_reg xmm_1) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_3) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_4) 32) (concat (fp_bitcast_to_bv (fp_div 1e+00 v_5) 32) (fp_bitcast_to_bv (fp_div 1e+00 v_6) 32))));
      pure ()
    pat_end

def rsqrtss : instruction :=
  definst "rsqrtss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 4;
      v_5 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single v_4));
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (fp_bitcast_to_bv (fp_div 1e+00 v_5) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      v_4 <- eval (bv_bitcast_to_fp float_class.fp32 (/- (_) -/ sqrt_single (extract v_3 96 128)));
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (fp_bitcast_to_bv (fp_div 1e+00 v_4) 32));
      pure ()
    pat_end

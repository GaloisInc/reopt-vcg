def rcpss : instruction :=
  definst "rcpss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      setRegister (lhs.of_reg xmm_1) (concat v_3 (fp_bitcast_to_bv (fp_div 1e+00 v_6) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      (v_3 : expression (bv 96)) <- eval (extract v_2 0 96);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      (v_5 : expression (bv 32)) <- eval (extract v_4 96 128);
      v_6 <- eval (bv_bitcast_to_fp float_class.fp32 v_5);
      setRegister (lhs.of_reg xmm_1) (concat v_3 (fp_bitcast_to_bv (fp_div 1e+00 v_6) 32));
      pure ()
    pat_end

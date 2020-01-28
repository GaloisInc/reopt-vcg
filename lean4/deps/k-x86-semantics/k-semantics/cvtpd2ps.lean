def cvtpd2ps : instruction :=
  definst "cvtpd2ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 0 64));
      v_5 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_3 64 128));
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (fp_bitcast_to_bv (fp_round v_4 24 8) 32) (fp_bitcast_to_bv (fp_round v_5 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      v_3 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_2 0 64));
      v_4 <- eval (bv_bitcast_to_fp float_class.fp64 (extract v_2 64 128));
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (fp_bitcast_to_bv (fp_round v_3 24 8) 32) (fp_bitcast_to_bv (fp_round v_4 24 8) 32)));
      pure ()
    pat_end

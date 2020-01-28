def vcvtpd2dqx : instruction :=
  definst "vcvtpd2dqx" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (/- (_) -/ cvt_double_to_int32_truncate (extract v_3 0 64)) (/- (_) -/ cvt_double_to_int32_truncate (extract v_3 64 128))));
      pure ()
    pat_end

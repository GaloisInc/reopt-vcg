def vcvtpd2dq : instruction :=
  definst "vcvtpd2dq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      setRegister (lhs.of_reg xmm_1) (concat (/- (_) -/ cvt_double_to_int32_truncate (extract v_3 0 64)) (concat (/- (_) -/ cvt_double_to_int32_truncate (extract v_3 64 128)) (concat (/- (_) -/ cvt_double_to_int32_truncate (extract v_3 128 192)) (/- (_) -/ cvt_double_to_int32_truncate (extract v_3 192 256)))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (/- (_) -/ cvt_double_to_int32_truncate (extract v_2 0 64)) (/- (_) -/ cvt_double_to_int32_truncate (extract v_2 64 128))));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg ymm_0);
      setRegister (lhs.of_reg xmm_1) (concat (/- (_) -/ cvt_double_to_int32_truncate (extract v_2 0 64)) (concat (/- (_) -/ cvt_double_to_int32_truncate (extract v_2 64 128)) (concat (/- (_) -/ cvt_double_to_int32_truncate (extract v_2 128 192)) (/- (_) -/ cvt_double_to_int32_truncate (extract v_2 192 256)))));
      pure ()
    pat_end

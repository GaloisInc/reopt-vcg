def cvttpd2dq : instruction :=
  definst "cvttpd2dq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 64)) <- eval (extract v_3 0 64);
      (v_5 : expression (bv 64)) <- eval (extract v_3 64 128);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (/- (_) -/ cvt_double_to_int32_truncate v_4) (/- (_) -/ cvt_double_to_int32_truncate v_5)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 64)) <- eval (extract v_2 0 64);
      (v_4 : expression (bv 64)) <- eval (extract v_2 64 128);
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (/- (_) -/ cvt_double_to_int32_truncate v_3) (/- (_) -/ cvt_double_to_int32_truncate v_4)));
      pure ()
    pat_end

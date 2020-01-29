def cvttps2dq : instruction :=
  definst "cvttps2dq" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      (v_4 : expression (bv 32)) <- eval (extract v_3 0 32);
      (v_5 : expression (bv 32)) <- eval (extract v_3 32 64);
      (v_6 : expression (bv 32)) <- eval (extract v_3 64 96);
      (v_7 : expression (bv 32)) <- eval (extract v_3 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (/- (_) -/ cvt_single_to_int32_truncate v_4) (concat (/- (_) -/ cvt_single_to_int32_truncate v_5) (concat (/- (_) -/ cvt_single_to_int32_truncate v_6) (/- (_) -/ cvt_single_to_int32_truncate v_7))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_0);
      (v_3 : expression (bv 32)) <- eval (extract v_2 0 32);
      (v_4 : expression (bv 32)) <- eval (extract v_2 32 64);
      (v_5 : expression (bv 32)) <- eval (extract v_2 64 96);
      (v_6 : expression (bv 32)) <- eval (extract v_2 96 128);
      setRegister (lhs.of_reg xmm_1) (concat (/- (_) -/ cvt_single_to_int32_truncate v_3) (concat (/- (_) -/ cvt_single_to_int32_truncate v_4) (concat (/- (_) -/ cvt_single_to_int32_truncate v_5) (/- (_) -/ cvt_single_to_int32_truncate v_6))));
      pure ()
    pat_end

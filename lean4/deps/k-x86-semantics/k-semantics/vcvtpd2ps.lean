def vcvtpd2ps1 : instruction :=
  definst "vcvtpd2ps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (roundFloat (MInt2Float (extract v_3 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_3 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_3 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_3 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_3 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_3 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (roundFloat (MInt2Float (extract v_3 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_3 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_3 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_3 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 32;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_3 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_3 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (concat (Float2MInt (roundFloat (MInt2Float (extract v_2 0 64) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_2 64 128) 53 11) 24 8) 32)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister ymm_0;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (roundFloat (MInt2Float (extract v_2 0 64) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_2 64 128) 53 11) 24 8) 32) (concat (Float2MInt (roundFloat (MInt2Float (extract v_2 128 192) 53 11) 24 8) 32) (Float2MInt (roundFloat (MInt2Float (extract v_2 192 256) 53 11) 24 8) 32))));
      pure ()
    pat_end

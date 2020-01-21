def cvtss2sd : instruction :=
  definst "cvtss2sd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 4;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (Float2MInt (roundFloat (MInt2Float v_4 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 64) (Float2MInt (roundFloat (MInt2Float (extract v_3 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end

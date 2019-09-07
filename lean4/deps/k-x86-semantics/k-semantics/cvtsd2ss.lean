def cvtsd2ss1 : instruction :=
  definst "cvtsd2ss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (Float2MInt (roundFloat (MInt2Float v_4 53 11) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (Float2MInt (roundFloat (MInt2Float (extract v_3 64 128) 53 11) 24 8) 32));
      pure ()
    pat_end

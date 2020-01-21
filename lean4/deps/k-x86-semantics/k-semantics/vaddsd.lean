def vaddsd : instruction :=
  definst "vaddsd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 8;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3 64 128) 53 11) (MInt2Float v_5 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_3 64 128) 53 11) (MInt2Float (extract v_4 64 128) 53 11)) 64));
      pure ()
    pat_end

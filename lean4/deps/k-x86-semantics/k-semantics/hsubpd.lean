def hsubpd1 : instruction :=
  definst "hsubpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 16;
      v_4 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3 64 128) 53 11) (MInt2Float (extract v_3 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4 64 128) 53 11) (MInt2Float (extract v_4 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      v_3 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_2 64 128) 53 11) (MInt2Float (extract v_2 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3 64 128) 53 11) (MInt2Float (extract v_3 0 64) 53 11)) 64));
      pure ()
    pat_end

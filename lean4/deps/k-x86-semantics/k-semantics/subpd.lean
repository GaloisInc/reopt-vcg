def subpd : instruction :=
  definst "subpd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_2 0 64) 53 11) (MInt2Float (extract v_4 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_2 64 128) 53 11) (MInt2Float (extract v_4 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_2 0 64) 53 11) (MInt2Float (extract v_3 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_2 64 128) 53 11) (MInt2Float (extract v_3 64 128) 53 11)) 64));
      pure ()
    pat_end

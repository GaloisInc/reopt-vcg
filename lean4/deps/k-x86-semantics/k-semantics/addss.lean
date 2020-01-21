def addss : instruction :=
  definst "addss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 4;
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_2 96 128) 24 8) (MInt2Float v_4 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister (lhs.of_reg xmm_1);
      v_3 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_1) (concat (extract v_2 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_2 96 128) 24 8) (MInt2Float (extract v_3 96 128) 24 8)) 32));
      pure ()
    pat_end

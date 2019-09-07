def divps1 : instruction :=
  definst "divps" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_2 0 32) 24 8) (MInt2Float (extract v_4 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_2 32 64) 24 8) (MInt2Float (extract v_4 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_2 64 96) 24 8) (MInt2Float (extract v_4 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_2 96 128) 24 8) (MInt2Float (extract v_4 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_2 0 32) 24 8) (MInt2Float (extract v_3 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_2 32 64) 24 8) (MInt2Float (extract v_3 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_2 64 96) 24 8) (MInt2Float (extract v_3 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_2 96 128) 24 8) (MInt2Float (extract v_3 96 128) 24 8)) 32))));
      pure ()
    pat_end

def vmulss : instruction :=
  definst "vmulss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_3 96 128) 24 8) (MInt2Float v_5 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_1);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_3 96 128) 24 8) (MInt2Float (extract v_4 96 128) 24 8)) 32));
      pure ()
    pat_end

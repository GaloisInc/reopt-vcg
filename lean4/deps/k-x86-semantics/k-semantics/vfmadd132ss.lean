def vfmadd132ss1 : instruction :=
  definst "vfmadd132ss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister xmm_2;
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 4;
      v_6 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 96 128) 24 8) (MInt2Float v_5 24 8)) (MInt2Float (extract v_6 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister xmm_2;
      v_4 <- getRegister xmm_0;
      v_5 <- getRegister xmm_1;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 96 128) 24 8) (MInt2Float (extract v_4 96 128) 24 8)) (MInt2Float (extract v_5 96 128) 24 8)) 32));
      pure ()
    pat_end

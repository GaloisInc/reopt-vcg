def vfmadd213ss : instruction :=
  definst "vfmadd213ss" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- evaluateAddress mem_0;
      v_6 <- load v_5 4;
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4 96 128) 24 8) (MInt2Float (extract v_3 96 128) 24 8)) (MInt2Float v_6 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_1);
      v_5 <- getRegister (lhs.of_reg xmm_0);
      setRegister (lhs.of_reg xmm_2) (concat (extract v_3 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4 96 128) 24 8) (MInt2Float (extract v_3 96 128) 24 8)) (MInt2Float (extract v_5 96 128) 24 8)) 32));
      pure ()
    pat_end

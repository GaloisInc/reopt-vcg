def vfmadd231ss1 : instruction :=
  definst "vfmadd231ss" $ do
    pattern fun (v_2670 : reg (bv 128)) (v_2671 : reg (bv 128)) (v_2672 : reg (bv 128)) => do
      v_4820 <- getRegister v_2672;
      v_4822 <- getRegister v_2671;
      v_4825 <- getRegister v_2670;
      setRegister (lhs.of_reg v_2672) (concat (extract v_4820 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4822 96 128) 24 8) (MInt2Float (extract v_4825 96 128) 24 8)) (MInt2Float (extract v_4820 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2664 : Mem) (v_2665 : reg (bv 128)) (v_2666 : reg (bv 128)) => do
      v_10781 <- getRegister v_2666;
      v_10783 <- getRegister v_2665;
      v_10786 <- evaluateAddress v_2664;
      v_10787 <- load v_10786 4;
      setRegister (lhs.of_reg v_2666) (concat (extract v_10781 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10783 96 128) 24 8) (MInt2Float v_10787 24 8)) (MInt2Float (extract v_10781 96 128) 24 8)) 32));
      pure ()
    pat_end

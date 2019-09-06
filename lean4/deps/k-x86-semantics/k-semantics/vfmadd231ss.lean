def vfmadd231ss1 : instruction :=
  definst "vfmadd231ss" $ do
    pattern fun (v_2694 : reg (bv 128)) (v_2695 : reg (bv 128)) (v_2696 : reg (bv 128)) => do
      v_4847 <- getRegister v_2696;
      v_4849 <- getRegister v_2695;
      v_4852 <- getRegister v_2694;
      setRegister (lhs.of_reg v_2696) (concat (extract v_4847 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_4849 96 128) 24 8) (MInt2Float (extract v_4852 96 128) 24 8)) (MInt2Float (extract v_4847 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2691 : Mem) (v_2689 : reg (bv 128)) (v_2690 : reg (bv 128)) => do
      v_10808 <- getRegister v_2690;
      v_10810 <- getRegister v_2689;
      v_10813 <- evaluateAddress v_2691;
      v_10814 <- load v_10813 4;
      setRegister (lhs.of_reg v_2690) (concat (extract v_10808 0 96) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_10810 96 128) 24 8) (MInt2Float v_10814 24 8)) (MInt2Float (extract v_10808 96 128) 24 8)) 32));
      pure ()
    pat_end

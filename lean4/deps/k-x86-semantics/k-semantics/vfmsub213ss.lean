def vfmsub213ss1 : instruction :=
  definst "vfmsub213ss" $ do
    pattern fun (v_2869 : reg (bv 128)) (v_2870 : reg (bv 128)) (v_2871 : reg (bv 128)) => do
      v_5881 <- getRegister v_2871;
      v_5883 <- getRegister v_2870;
      v_5889 <- getRegister v_2869;
      setRegister (lhs.of_reg v_2871) (concat (extract v_5881 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5883 96 128) 24 8) (MInt2Float (extract v_5881 96 128) 24 8)) (MInt2Float (extract v_5889 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2866 : Mem) (v_2864 : reg (bv 128)) (v_2865 : reg (bv 128)) => do
      v_11725 <- getRegister v_2865;
      v_11727 <- getRegister v_2864;
      v_11733 <- evaluateAddress v_2866;
      v_11734 <- load v_11733 4;
      setRegister (lhs.of_reg v_2865) (concat (extract v_11725 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11727 96 128) 24 8) (MInt2Float (extract v_11725 96 128) 24 8)) (MInt2Float v_11734 24 8)) 32));
      pure ()
    pat_end

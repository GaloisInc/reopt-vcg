def vfmsub213ss1 : instruction :=
  definst "vfmsub213ss" $ do
    pattern fun (v_2958 : reg (bv 128)) (v_2959 : reg (bv 128)) (v_2960 : reg (bv 128)) => do
      v_5975 <- getRegister v_2960;
      v_5977 <- getRegister v_2959;
      v_5983 <- getRegister v_2958;
      setRegister (lhs.of_reg v_2960) (concat (extract v_5975 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5977 96 128) 24 8) (MInt2Float (extract v_5975 96 128) 24 8)) (MInt2Float (extract v_5983 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2955 : Mem) (v_2953 : reg (bv 128)) (v_2954 : reg (bv 128)) => do
      v_11836 <- getRegister v_2954;
      v_11838 <- getRegister v_2953;
      v_11844 <- evaluateAddress v_2955;
      v_11845 <- load v_11844 4;
      setRegister (lhs.of_reg v_2954) (concat (extract v_11836 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11838 96 128) 24 8) (MInt2Float (extract v_11836 96 128) 24 8)) (MInt2Float v_11845 24 8)) 32));
      pure ()
    pat_end

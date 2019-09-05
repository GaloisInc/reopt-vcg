def vfmsub213ss1 : instruction :=
  definst "vfmsub213ss" $ do
    pattern fun (v_2934 : reg (bv 128)) (v_2935 : reg (bv 128)) (v_2936 : reg (bv 128)) => do
      v_5948 <- getRegister v_2936;
      v_5950 <- getRegister v_2935;
      v_5956 <- getRegister v_2934;
      setRegister (lhs.of_reg v_2936) (concat (extract v_5948 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5950 96 128) 24 8) (MInt2Float (extract v_5948 96 128) 24 8)) (MInt2Float (extract v_5956 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2928 : Mem) (v_2929 : reg (bv 128)) (v_2930 : reg (bv 128)) => do
      v_11809 <- getRegister v_2930;
      v_11811 <- getRegister v_2929;
      v_11817 <- evaluateAddress v_2928;
      v_11818 <- load v_11817 4;
      setRegister (lhs.of_reg v_2930) (concat (extract v_11809 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11811 96 128) 24 8) (MInt2Float (extract v_11809 96 128) 24 8)) (MInt2Float v_11818 24 8)) 32));
      pure ()
    pat_end

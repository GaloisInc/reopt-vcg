def vfmsub213sd1 : instruction :=
  definst "vfmsub213sd" $ do
    pattern fun (v_2858 : reg (bv 128)) (v_2859 : reg (bv 128)) (v_2860 : reg (bv 128)) => do
      v_5861 <- getRegister v_2860;
      v_5863 <- getRegister v_2859;
      v_5869 <- getRegister v_2858;
      setRegister (lhs.of_reg v_2860) (concat (extract v_5861 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5863 64 128) 53 11) (MInt2Float (extract v_5861 64 128) 53 11)) (MInt2Float (extract v_5869 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2855 : Mem) (v_2853 : reg (bv 128)) (v_2854 : reg (bv 128)) => do
      v_11710 <- getRegister v_2854;
      v_11712 <- getRegister v_2853;
      v_11718 <- evaluateAddress v_2855;
      v_11719 <- load v_11718 8;
      setRegister (lhs.of_reg v_2854) (concat (extract v_11710 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11712 64 128) 53 11) (MInt2Float (extract v_11710 64 128) 53 11)) (MInt2Float v_11719 53 11)) 64));
      pure ()
    pat_end

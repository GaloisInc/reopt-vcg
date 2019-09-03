def vfmsub231sd1 : instruction :=
  definst "vfmsub231sd" $ do
    pattern fun (v_2924 : reg (bv 128)) (v_2925 : reg (bv 128)) (v_2926 : reg (bv 128)) => do
      v_6113 <- getRegister v_2926;
      v_6115 <- getRegister v_2925;
      v_6118 <- getRegister v_2924;
      setRegister (lhs.of_reg v_2926) (concat (extract v_6113 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6115 64 128) 53 11) (MInt2Float (extract v_6118 64 128) 53 11)) (MInt2Float (extract v_6113 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2921 : Mem) (v_2919 : reg (bv 128)) (v_2920 : reg (bv 128)) => do
      v_11936 <- getRegister v_2920;
      v_11938 <- getRegister v_2919;
      v_11941 <- evaluateAddress v_2921;
      v_11942 <- load v_11941 8;
      setRegister (lhs.of_reg v_2920) (concat (extract v_11936 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11938 64 128) 53 11) (MInt2Float v_11942 53 11)) (MInt2Float (extract v_11936 64 128) 53 11)) 64));
      pure ()
    pat_end

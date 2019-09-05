def vfmsub213sd1 : instruction :=
  definst "vfmsub213sd" $ do
    pattern fun (v_2923 : reg (bv 128)) (v_2924 : reg (bv 128)) (v_2925 : reg (bv 128)) => do
      v_5928 <- getRegister v_2925;
      v_5930 <- getRegister v_2924;
      v_5936 <- getRegister v_2923;
      setRegister (lhs.of_reg v_2925) (concat (extract v_5928 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5930 64 128) 53 11) (MInt2Float (extract v_5928 64 128) 53 11)) (MInt2Float (extract v_5936 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2917 : Mem) (v_2918 : reg (bv 128)) (v_2919 : reg (bv 128)) => do
      v_11794 <- getRegister v_2919;
      v_11796 <- getRegister v_2918;
      v_11802 <- evaluateAddress v_2917;
      v_11803 <- load v_11802 8;
      setRegister (lhs.of_reg v_2919) (concat (extract v_11794 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11796 64 128) 53 11) (MInt2Float (extract v_11794 64 128) 53 11)) (MInt2Float v_11803 53 11)) 64));
      pure ()
    pat_end

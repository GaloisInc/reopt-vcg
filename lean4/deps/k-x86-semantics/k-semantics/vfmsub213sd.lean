def vfmsub213sd1 : instruction :=
  definst "vfmsub213sd" $ do
    pattern fun (v_2947 : reg (bv 128)) (v_2948 : reg (bv 128)) (v_2949 : reg (bv 128)) => do
      v_5955 <- getRegister v_2949;
      v_5957 <- getRegister v_2948;
      v_5963 <- getRegister v_2947;
      setRegister (lhs.of_reg v_2949) (concat (extract v_5955 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5957 64 128) 53 11) (MInt2Float (extract v_5955 64 128) 53 11)) (MInt2Float (extract v_5963 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2944 : Mem) (v_2942 : reg (bv 128)) (v_2943 : reg (bv 128)) => do
      v_11821 <- getRegister v_2943;
      v_11823 <- getRegister v_2942;
      v_11829 <- evaluateAddress v_2944;
      v_11830 <- load v_11829 8;
      setRegister (lhs.of_reg v_2943) (concat (extract v_11821 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11823 64 128) 53 11) (MInt2Float (extract v_11821 64 128) 53 11)) (MInt2Float v_11830 53 11)) 64));
      pure ()
    pat_end

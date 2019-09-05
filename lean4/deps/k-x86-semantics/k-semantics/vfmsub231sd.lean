def vfmsub231sd1 : instruction :=
  definst "vfmsub231sd" $ do
    pattern fun (v_2989 : reg (bv 128)) (v_2990 : reg (bv 128)) (v_2991 : reg (bv 128)) => do
      v_6180 <- getRegister v_2991;
      v_6182 <- getRegister v_2990;
      v_6185 <- getRegister v_2989;
      setRegister (lhs.of_reg v_2991) (concat (extract v_6180 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6182 64 128) 53 11) (MInt2Float (extract v_6185 64 128) 53 11)) (MInt2Float (extract v_6180 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2983 : Mem) (v_2984 : reg (bv 128)) (v_2985 : reg (bv 128)) => do
      v_12020 <- getRegister v_2985;
      v_12022 <- getRegister v_2984;
      v_12025 <- evaluateAddress v_2983;
      v_12026 <- load v_12025 8;
      setRegister (lhs.of_reg v_2985) (concat (extract v_12020 0 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12022 64 128) 53 11) (MInt2Float v_12026 53 11)) (MInt2Float (extract v_12020 64 128) 53 11)) 64));
      pure ()
    pat_end

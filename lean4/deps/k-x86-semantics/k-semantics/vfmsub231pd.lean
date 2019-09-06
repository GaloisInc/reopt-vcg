def vfmsub231pd1 : instruction :=
  definst "vfmsub231pd" $ do
    pattern fun (v_2969 : reg (bv 128)) (v_2970 : reg (bv 128)) (v_2971 : reg (bv 128)) => do
      v_5995 <- getRegister v_2970;
      v_5998 <- getRegister v_2969;
      v_6002 <- getRegister v_2971;
      setRegister (lhs.of_reg v_2971) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5995 0 64) 53 11) (MInt2Float (extract v_5998 0 64) 53 11)) (MInt2Float (extract v_6002 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5995 64 128) 53 11) (MInt2Float (extract v_5998 64 128) 53 11)) (MInt2Float (extract v_6002 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2983 : reg (bv 256)) (v_2984 : reg (bv 256)) (v_2985 : reg (bv 256)) => do
      v_6023 <- getRegister v_2984;
      v_6026 <- getRegister v_2983;
      v_6030 <- getRegister v_2985;
      setRegister (lhs.of_reg v_2985) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6023 0 64) 53 11) (MInt2Float (extract v_6026 0 64) 53 11)) (MInt2Float (extract v_6030 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6023 64 128) 53 11) (MInt2Float (extract v_6026 64 128) 53 11)) (MInt2Float (extract v_6030 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6023 128 192) 53 11) (MInt2Float (extract v_6026 128 192) 53 11)) (MInt2Float (extract v_6030 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6023 192 256) 53 11) (MInt2Float (extract v_6026 192 256) 53 11)) (MInt2Float (extract v_6030 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2966 : Mem) (v_2964 : reg (bv 128)) (v_2965 : reg (bv 128)) => do
      v_11851 <- getRegister v_2964;
      v_11854 <- evaluateAddress v_2966;
      v_11855 <- load v_11854 16;
      v_11859 <- getRegister v_2965;
      setRegister (lhs.of_reg v_2965) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11851 0 64) 53 11) (MInt2Float (extract v_11855 0 64) 53 11)) (MInt2Float (extract v_11859 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11851 64 128) 53 11) (MInt2Float (extract v_11855 64 128) 53 11)) (MInt2Float (extract v_11859 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2975 : Mem) (v_2978 : reg (bv 256)) (v_2979 : reg (bv 256)) => do
      v_11875 <- getRegister v_2978;
      v_11878 <- evaluateAddress v_2975;
      v_11879 <- load v_11878 32;
      v_11883 <- getRegister v_2979;
      setRegister (lhs.of_reg v_2979) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11875 0 64) 53 11) (MInt2Float (extract v_11879 0 64) 53 11)) (MInt2Float (extract v_11883 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11875 64 128) 53 11) (MInt2Float (extract v_11879 64 128) 53 11)) (MInt2Float (extract v_11883 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11875 128 192) 53 11) (MInt2Float (extract v_11879 128 192) 53 11)) (MInt2Float (extract v_11883 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11875 192 256) 53 11) (MInt2Float (extract v_11879 192 256) 53 11)) (MInt2Float (extract v_11883 192 256) 53 11)) 64)));
      pure ()
    pat_end

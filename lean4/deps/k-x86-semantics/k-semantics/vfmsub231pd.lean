def vfmsub231pd1 : instruction :=
  definst "vfmsub231pd" $ do
    pattern fun (v_2945 : reg (bv 128)) (v_2946 : reg (bv 128)) (v_2947 : reg (bv 128)) => do
      v_5968 <- getRegister v_2946;
      v_5971 <- getRegister v_2945;
      v_5975 <- getRegister v_2947;
      setRegister (lhs.of_reg v_2947) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5968 0 64) 53 11) (MInt2Float (extract v_5971 0 64) 53 11)) (MInt2Float (extract v_5975 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5968 64 128) 53 11) (MInt2Float (extract v_5971 64 128) 53 11)) (MInt2Float (extract v_5975 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2955 : reg (bv 256)) (v_2956 : reg (bv 256)) (v_2957 : reg (bv 256)) => do
      v_5996 <- getRegister v_2956;
      v_5999 <- getRegister v_2955;
      v_6003 <- getRegister v_2957;
      setRegister (lhs.of_reg v_2957) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5996 0 64) 53 11) (MInt2Float (extract v_5999 0 64) 53 11)) (MInt2Float (extract v_6003 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5996 64 128) 53 11) (MInt2Float (extract v_5999 64 128) 53 11)) (MInt2Float (extract v_6003 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5996 128 192) 53 11) (MInt2Float (extract v_5999 128 192) 53 11)) (MInt2Float (extract v_6003 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_5996 192 256) 53 11) (MInt2Float (extract v_5999 192 256) 53 11)) (MInt2Float (extract v_6003 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_2939 : Mem) (v_2940 : reg (bv 128)) (v_2941 : reg (bv 128)) => do
      v_11824 <- getRegister v_2940;
      v_11827 <- evaluateAddress v_2939;
      v_11828 <- load v_11827 16;
      v_11832 <- getRegister v_2941;
      setRegister (lhs.of_reg v_2941) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11824 0 64) 53 11) (MInt2Float (extract v_11828 0 64) 53 11)) (MInt2Float (extract v_11832 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11824 64 128) 53 11) (MInt2Float (extract v_11828 64 128) 53 11)) (MInt2Float (extract v_11832 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2950 : Mem) (v_2951 : reg (bv 256)) (v_2952 : reg (bv 256)) => do
      v_11848 <- getRegister v_2951;
      v_11851 <- evaluateAddress v_2950;
      v_11852 <- load v_11851 32;
      v_11856 <- getRegister v_2952;
      setRegister (lhs.of_reg v_2952) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11848 0 64) 53 11) (MInt2Float (extract v_11852 0 64) 53 11)) (MInt2Float (extract v_11856 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11848 64 128) 53 11) (MInt2Float (extract v_11852 64 128) 53 11)) (MInt2Float (extract v_11856 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11848 128 192) 53 11) (MInt2Float (extract v_11852 128 192) 53 11)) (MInt2Float (extract v_11856 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_11848 192 256) 53 11) (MInt2Float (extract v_11852 192 256) 53 11)) (MInt2Float (extract v_11856 192 256) 53 11)) 64)));
      pure ()
    pat_end

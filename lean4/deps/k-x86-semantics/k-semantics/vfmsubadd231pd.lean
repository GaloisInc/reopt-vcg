def vfmsubadd231pd1 : instruction :=
  definst "vfmsubadd231pd" $ do
    pattern fun (v_3034 : reg (bv 128)) (v_3035 : reg (bv 128)) (v_3036 : reg (bv 128)) => do
      v_6562 <- getRegister v_3035;
      v_6565 <- getRegister v_3034;
      v_6569 <- getRegister v_3036;
      setRegister (lhs.of_reg v_3036) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6562 0 64) 53 11) (MInt2Float (extract v_6565 0 64) 53 11)) (MInt2Float (extract v_6569 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6562 64 128) 53 11) (MInt2Float (extract v_6565 64 128) 53 11)) (MInt2Float (extract v_6569 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3046 : reg (bv 256)) (v_3047 : reg (bv 256)) (v_3048 : reg (bv 256)) => do
      v_6590 <- getRegister v_3047;
      v_6593 <- getRegister v_3046;
      v_6597 <- getRegister v_3048;
      setRegister (lhs.of_reg v_3048) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6590 0 64) 53 11) (MInt2Float (extract v_6593 0 64) 53 11)) (MInt2Float (extract v_6597 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6590 64 128) 53 11) (MInt2Float (extract v_6593 64 128) 53 11)) (MInt2Float (extract v_6597 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6590 128 192) 53 11) (MInt2Float (extract v_6593 128 192) 53 11)) (MInt2Float (extract v_6597 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6590 192 256) 53 11) (MInt2Float (extract v_6593 192 256) 53 11)) (MInt2Float (extract v_6597 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_3031 : Mem) (v_3029 : reg (bv 128)) (v_3030 : reg (bv 128)) => do
      v_12343 <- getRegister v_3029;
      v_12346 <- evaluateAddress v_3031;
      v_12347 <- load v_12346 16;
      v_12351 <- getRegister v_3030;
      setRegister (lhs.of_reg v_3030) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 0 64) 53 11) (MInt2Float (extract v_12347 0 64) 53 11)) (MInt2Float (extract v_12351 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12343 64 128) 53 11) (MInt2Float (extract v_12347 64 128) 53 11)) (MInt2Float (extract v_12351 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3040 : Mem) (v_3041 : reg (bv 256)) (v_3042 : reg (bv 256)) => do
      v_12367 <- getRegister v_3041;
      v_12370 <- evaluateAddress v_3040;
      v_12371 <- load v_12370 32;
      v_12375 <- getRegister v_3042;
      setRegister (lhs.of_reg v_3042) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12367 0 64) 53 11) (MInt2Float (extract v_12371 0 64) 53 11)) (MInt2Float (extract v_12375 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12367 64 128) 53 11) (MInt2Float (extract v_12371 64 128) 53 11)) (MInt2Float (extract v_12375 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12367 128 192) 53 11) (MInt2Float (extract v_12371 128 192) 53 11)) (MInt2Float (extract v_12375 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12367 192 256) 53 11) (MInt2Float (extract v_12371 192 256) 53 11)) (MInt2Float (extract v_12375 192 256) 53 11)) 64)));
      pure ()
    pat_end

def vfmsubadd213pd1 : instruction :=
  definst "vfmsubadd213pd" $ do
    pattern fun (v_3055 : reg (bv 128)) (v_3056 : reg (bv 128)) (v_3057 : reg (bv 128)) => do
      v_6417 <- getRegister v_3056;
      v_6420 <- getRegister v_3057;
      v_6424 <- getRegister v_3055;
      setRegister (lhs.of_reg v_3057) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6417 0 64) 53 11) (MInt2Float (extract v_6420 0 64) 53 11)) (MInt2Float (extract v_6424 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6417 64 128) 53 11) (MInt2Float (extract v_6420 64 128) 53 11)) (MInt2Float (extract v_6424 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3065 : reg (bv 256)) (v_3066 : reg (bv 256)) (v_3067 : reg (bv 256)) => do
      v_6445 <- getRegister v_3066;
      v_6448 <- getRegister v_3067;
      v_6452 <- getRegister v_3065;
      setRegister (lhs.of_reg v_3067) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6445 0 64) 53 11) (MInt2Float (extract v_6448 0 64) 53 11)) (MInt2Float (extract v_6452 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6445 64 128) 53 11) (MInt2Float (extract v_6448 64 128) 53 11)) (MInt2Float (extract v_6452 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6445 128 192) 53 11) (MInt2Float (extract v_6448 128 192) 53 11)) (MInt2Float (extract v_6452 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6445 192 256) 53 11) (MInt2Float (extract v_6448 192 256) 53 11)) (MInt2Float (extract v_6452 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_3049 : Mem) (v_3050 : reg (bv 128)) (v_3051 : reg (bv 128)) => do
      v_12231 <- getRegister v_3050;
      v_12234 <- getRegister v_3051;
      v_12238 <- evaluateAddress v_3049;
      v_12239 <- load v_12238 16;
      setRegister (lhs.of_reg v_3051) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12231 0 64) 53 11) (MInt2Float (extract v_12234 0 64) 53 11)) (MInt2Float (extract v_12239 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12231 64 128) 53 11) (MInt2Float (extract v_12234 64 128) 53 11)) (MInt2Float (extract v_12239 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3060 : Mem) (v_3061 : reg (bv 256)) (v_3062 : reg (bv 256)) => do
      v_12255 <- getRegister v_3061;
      v_12258 <- getRegister v_3062;
      v_12262 <- evaluateAddress v_3060;
      v_12263 <- load v_12262 32;
      setRegister (lhs.of_reg v_3062) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12255 0 64) 53 11) (MInt2Float (extract v_12258 0 64) 53 11)) (MInt2Float (extract v_12263 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12255 64 128) 53 11) (MInt2Float (extract v_12258 64 128) 53 11)) (MInt2Float (extract v_12263 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12255 128 192) 53 11) (MInt2Float (extract v_12258 128 192) 53 11)) (MInt2Float (extract v_12263 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12255 192 256) 53 11) (MInt2Float (extract v_12258 192 256) 53 11)) (MInt2Float (extract v_12263 192 256) 53 11)) 64)));
      pure ()
    pat_end

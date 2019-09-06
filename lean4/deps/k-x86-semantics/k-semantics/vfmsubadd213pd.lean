def vfmsubadd213pd1 : instruction :=
  definst "vfmsubadd213pd" $ do
    pattern fun (v_3079 : reg (bv 128)) (v_3080 : reg (bv 128)) (v_3081 : reg (bv 128)) => do
      v_6444 <- getRegister v_3080;
      v_6447 <- getRegister v_3081;
      v_6451 <- getRegister v_3079;
      setRegister (lhs.of_reg v_3081) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6444 0 64) 53 11) (MInt2Float (extract v_6447 0 64) 53 11)) (MInt2Float (extract v_6451 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6444 64 128) 53 11) (MInt2Float (extract v_6447 64 128) 53 11)) (MInt2Float (extract v_6451 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3093 : reg (bv 256)) (v_3094 : reg (bv 256)) (v_3095 : reg (bv 256)) => do
      v_6472 <- getRegister v_3094;
      v_6475 <- getRegister v_3095;
      v_6479 <- getRegister v_3093;
      setRegister (lhs.of_reg v_3095) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6472 0 64) 53 11) (MInt2Float (extract v_6475 0 64) 53 11)) (MInt2Float (extract v_6479 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6472 64 128) 53 11) (MInt2Float (extract v_6475 64 128) 53 11)) (MInt2Float (extract v_6479 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6472 128 192) 53 11) (MInt2Float (extract v_6475 128 192) 53 11)) (MInt2Float (extract v_6479 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6472 192 256) 53 11) (MInt2Float (extract v_6475 192 256) 53 11)) (MInt2Float (extract v_6479 192 256) 53 11)) 64)));
      pure ()
    pat_end;
    pattern fun (v_3076 : Mem) (v_3074 : reg (bv 128)) (v_3075 : reg (bv 128)) => do
      v_12258 <- getRegister v_3074;
      v_12261 <- getRegister v_3075;
      v_12265 <- evaluateAddress v_3076;
      v_12266 <- load v_12265 16;
      setRegister (lhs.of_reg v_3075) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12258 0 64) 53 11) (MInt2Float (extract v_12261 0 64) 53 11)) (MInt2Float (extract v_12266 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12258 64 128) 53 11) (MInt2Float (extract v_12261 64 128) 53 11)) (MInt2Float (extract v_12266 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3085 : Mem) (v_3088 : reg (bv 256)) (v_3089 : reg (bv 256)) => do
      v_12282 <- getRegister v_3088;
      v_12285 <- getRegister v_3089;
      v_12289 <- evaluateAddress v_3085;
      v_12290 <- load v_12289 32;
      setRegister (lhs.of_reg v_3089) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12282 0 64) 53 11) (MInt2Float (extract v_12285 0 64) 53 11)) (MInt2Float (extract v_12290 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12282 64 128) 53 11) (MInt2Float (extract v_12285 64 128) 53 11)) (MInt2Float (extract v_12290 64 128) 53 11)) 64)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12282 128 192) 53 11) (MInt2Float (extract v_12285 128 192) 53 11)) (MInt2Float (extract v_12290 128 192) 53 11)) 64) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12282 192 256) 53 11) (MInt2Float (extract v_12285 192 256) 53 11)) (MInt2Float (extract v_12290 192 256) 53 11)) 64)));
      pure ()
    pat_end

def vsubpd1 : instruction :=
  definst "vsubpd" $ do
    pattern fun (v_3080 : reg (bv 128)) (v_3081 : reg (bv 128)) (v_3082 : reg (bv 128)) => do
      v_7102 <- getRegister v_3081;
      v_7105 <- getRegister v_3080;
      setRegister (lhs.of_reg v_3082) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7102 0 64) 53 11) (MInt2Float (extract v_7105 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7102 64 128) 53 11) (MInt2Float (extract v_7105 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3091 : reg (bv 256)) (v_3092 : reg (bv 256)) (v_3093 : reg (bv 256)) => do
      v_7123 <- getRegister v_3092;
      v_7126 <- getRegister v_3091;
      setRegister (lhs.of_reg v_3093) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7123 0 64) 53 11) (MInt2Float (extract v_7126 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7123 64 128) 53 11) (MInt2Float (extract v_7126 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7123 128 192) 53 11) (MInt2Float (extract v_7126 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7123 192 256) 53 11) (MInt2Float (extract v_7126 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3074 : Mem) (v_3075 : reg (bv 128)) (v_3076 : reg (bv 128)) => do
      v_13028 <- getRegister v_3075;
      v_13031 <- evaluateAddress v_3074;
      v_13032 <- load v_13031 16;
      setRegister (lhs.of_reg v_3076) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13028 0 64) 53 11) (MInt2Float (extract v_13032 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13028 64 128) 53 11) (MInt2Float (extract v_13032 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3085 : Mem) (v_3086 : reg (bv 256)) (v_3087 : reg (bv 256)) => do
      v_13045 <- getRegister v_3086;
      v_13048 <- evaluateAddress v_3085;
      v_13049 <- load v_13048 32;
      setRegister (lhs.of_reg v_3087) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13045 0 64) 53 11) (MInt2Float (extract v_13049 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13045 64 128) 53 11) (MInt2Float (extract v_13049 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13045 128 192) 53 11) (MInt2Float (extract v_13049 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13045 192 256) 53 11) (MInt2Float (extract v_13049 192 256) 53 11)) 64))));
      pure ()
    pat_end

def vmulpd1 : instruction :=
  definst "vmulpd" $ do
    pattern fun (v_3133 : reg (bv 128)) (v_3134 : reg (bv 128)) (v_3135 : reg (bv 128)) => do
      v_5154 <- getRegister v_3134;
      v_5157 <- getRegister v_3133;
      setRegister (lhs.of_reg v_3135) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5154 0 64) 53 11) (MInt2Float (extract v_5157 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5154 64 128) 53 11) (MInt2Float (extract v_5157 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3145 : reg (bv 256)) (v_3146 : reg (bv 256)) (v_3147 : reg (bv 256)) => do
      v_5175 <- getRegister v_3146;
      v_5178 <- getRegister v_3145;
      setRegister (lhs.of_reg v_3147) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5175 0 64) 53 11) (MInt2Float (extract v_5178 0 64) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5175 64 128) 53 11) (MInt2Float (extract v_5178 64 128) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5175 128 192) 53 11) (MInt2Float (extract v_5178 128 192) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5175 192 256) 53 11) (MInt2Float (extract v_5178 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3128 : Mem) (v_3129 : reg (bv 128)) (v_3130 : reg (bv 128)) => do
      v_10286 <- getRegister v_3129;
      v_10289 <- evaluateAddress v_3128;
      v_10290 <- load v_10289 16;
      setRegister (lhs.of_reg v_3130) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10286 0 64) 53 11) (MInt2Float (extract v_10290 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10286 64 128) 53 11) (MInt2Float (extract v_10290 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3139 : Mem) (v_3140 : reg (bv 256)) (v_3141 : reg (bv 256)) => do
      v_10303 <- getRegister v_3140;
      v_10306 <- evaluateAddress v_3139;
      v_10307 <- load v_10306 32;
      setRegister (lhs.of_reg v_3141) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10303 0 64) 53 11) (MInt2Float (extract v_10307 0 64) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10303 64 128) 53 11) (MInt2Float (extract v_10307 64 128) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10303 128 192) 53 11) (MInt2Float (extract v_10307 128 192) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10303 192 256) 53 11) (MInt2Float (extract v_10307 192 256) 53 11)) 64))));
      pure ()
    pat_end

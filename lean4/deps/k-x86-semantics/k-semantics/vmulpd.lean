def vmulpd1 : instruction :=
  definst "vmulpd" $ do
    pattern fun (v_3158 : reg (bv 128)) (v_3159 : reg (bv 128)) (v_3160 : reg (bv 128)) => do
      v_5181 <- getRegister v_3159;
      v_5184 <- getRegister v_3158;
      setRegister (lhs.of_reg v_3160) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5181 0 64) 53 11) (MInt2Float (extract v_5184 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5181 64 128) 53 11) (MInt2Float (extract v_5184 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3169 : reg (bv 256)) (v_3170 : reg (bv 256)) (v_3171 : reg (bv 256)) => do
      v_5202 <- getRegister v_3170;
      v_5205 <- getRegister v_3169;
      setRegister (lhs.of_reg v_3171) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5202 0 64) 53 11) (MInt2Float (extract v_5205 0 64) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5202 64 128) 53 11) (MInt2Float (extract v_5205 64 128) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5202 128 192) 53 11) (MInt2Float (extract v_5205 128 192) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5202 192 256) 53 11) (MInt2Float (extract v_5205 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3153 : Mem) (v_3154 : reg (bv 128)) (v_3155 : reg (bv 128)) => do
      v_10313 <- getRegister v_3154;
      v_10316 <- evaluateAddress v_3153;
      v_10317 <- load v_10316 16;
      setRegister (lhs.of_reg v_3155) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10313 0 64) 53 11) (MInt2Float (extract v_10317 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10313 64 128) 53 11) (MInt2Float (extract v_10317 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3164 : Mem) (v_3165 : reg (bv 256)) (v_3166 : reg (bv 256)) => do
      v_10330 <- getRegister v_3165;
      v_10333 <- evaluateAddress v_3164;
      v_10334 <- load v_10333 32;
      setRegister (lhs.of_reg v_3166) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10330 0 64) 53 11) (MInt2Float (extract v_10334 0 64) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10330 64 128) 53 11) (MInt2Float (extract v_10334 64 128) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10330 128 192) 53 11) (MInt2Float (extract v_10334 128 192) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10330 192 256) 53 11) (MInt2Float (extract v_10334 192 256) 53 11)) 64))));
      pure ()
    pat_end

def vmulpd1 : instruction :=
  definst "vmulpd" $ do
    pattern fun (v_3070 : reg (bv 128)) (v_3071 : reg (bv 128)) (v_3072 : reg (bv 128)) => do
      v_5096 <- getRegister v_3071;
      v_5099 <- getRegister v_3070;
      setRegister (lhs.of_reg v_3072) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5096 0 64) 53 11) (MInt2Float (extract v_5099 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5096 64 128) 53 11) (MInt2Float (extract v_5099 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3081 : reg (bv 256)) (v_3082 : reg (bv 256)) (v_3083 : reg (bv 256)) => do
      v_5117 <- getRegister v_3082;
      v_5120 <- getRegister v_3081;
      setRegister (lhs.of_reg v_3083) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5117 0 64) 53 11) (MInt2Float (extract v_5120 0 64) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5117 64 128) 53 11) (MInt2Float (extract v_5120 64 128) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5117 128 192) 53 11) (MInt2Float (extract v_5120 128 192) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_5117 192 256) 53 11) (MInt2Float (extract v_5120 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3064 : Mem) (v_3065 : reg (bv 128)) (v_3066 : reg (bv 128)) => do
      v_10420 <- getRegister v_3065;
      v_10423 <- evaluateAddress v_3064;
      v_10424 <- load v_10423 16;
      setRegister (lhs.of_reg v_3066) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10420 0 64) 53 11) (MInt2Float (extract v_10424 0 64) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10420 64 128) 53 11) (MInt2Float (extract v_10424 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3075 : Mem) (v_3076 : reg (bv 256)) (v_3077 : reg (bv 256)) => do
      v_10437 <- getRegister v_3076;
      v_10440 <- evaluateAddress v_3075;
      v_10441 <- load v_10440 32;
      setRegister (lhs.of_reg v_3077) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10437 0 64) 53 11) (MInt2Float (extract v_10441 0 64) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10437 64 128) 53 11) (MInt2Float (extract v_10441 64 128) 53 11)) 64) (concat (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10437 128 192) 53 11) (MInt2Float (extract v_10441 128 192) 53 11)) 64) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_10437 192 256) 53 11) (MInt2Float (extract v_10441 192 256) 53 11)) 64))));
      pure ()
    pat_end

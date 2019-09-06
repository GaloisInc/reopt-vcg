def vsubpd1 : instruction :=
  definst "vsubpd" $ do
    pattern fun (v_3107 : reg (bv 128)) (v_3108 : reg (bv 128)) (v_3109 : reg (bv 128)) => do
      v_7129 <- getRegister v_3108;
      v_7132 <- getRegister v_3107;
      setRegister (lhs.of_reg v_3109) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7129 0 64) 53 11) (MInt2Float (extract v_7132 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7129 64 128) 53 11) (MInt2Float (extract v_7132 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3118 : reg (bv 256)) (v_3119 : reg (bv 256)) (v_3120 : reg (bv 256)) => do
      v_7150 <- getRegister v_3119;
      v_7153 <- getRegister v_3118;
      setRegister (lhs.of_reg v_3120) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7150 0 64) 53 11) (MInt2Float (extract v_7153 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7150 64 128) 53 11) (MInt2Float (extract v_7153 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7150 128 192) 53 11) (MInt2Float (extract v_7153 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7150 192 256) 53 11) (MInt2Float (extract v_7153 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3101 : Mem) (v_3102 : reg (bv 128)) (v_3103 : reg (bv 128)) => do
      v_13055 <- getRegister v_3102;
      v_13058 <- evaluateAddress v_3101;
      v_13059 <- load v_13058 16;
      setRegister (lhs.of_reg v_3103) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13055 0 64) 53 11) (MInt2Float (extract v_13059 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13055 64 128) 53 11) (MInt2Float (extract v_13059 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3112 : Mem) (v_3113 : reg (bv 256)) (v_3114 : reg (bv 256)) => do
      v_13072 <- getRegister v_3113;
      v_13075 <- evaluateAddress v_3112;
      v_13076 <- load v_13075 32;
      setRegister (lhs.of_reg v_3114) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13072 0 64) 53 11) (MInt2Float (extract v_13076 0 64) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13072 64 128) 53 11) (MInt2Float (extract v_13076 64 128) 53 11)) 64) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13072 128 192) 53 11) (MInt2Float (extract v_13076 128 192) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_13072 192 256) 53 11) (MInt2Float (extract v_13076 192 256) 53 11)) 64))));
      pure ()
    pat_end

def subpd1 : instruction :=
  definst "subpd" $ do
    pattern fun (v_3179 : reg (bv 128)) (v_3180 : reg (bv 128)) => do
      v_7231 <- getRegister v_3180;
      v_7234 <- getRegister v_3179;
      setRegister (lhs.of_reg v_3180) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7231 0 64) 53 11) (MInt2Float (extract v_7234 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_7231 64 128) 53 11) (MInt2Float (extract v_7234 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3174 : Mem) (v_3175 : reg (bv 128)) => do
      v_10417 <- getRegister v_3175;
      v_10420 <- evaluateAddress v_3174;
      v_10421 <- load v_10420 16;
      setRegister (lhs.of_reg v_3175) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_10417 0 64) 53 11) (MInt2Float (extract v_10421 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_10417 64 128) 53 11) (MInt2Float (extract v_10421 64 128) 53 11)) 64));
      pure ()
    pat_end

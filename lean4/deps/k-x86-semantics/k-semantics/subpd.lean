def subpd1 : instruction :=
  definst "subpd" $ do
    pattern fun (v_3242 : reg (bv 128)) (v_3243 : reg (bv 128)) => do
      v_6444 <- getRegister v_3243;
      v_6447 <- getRegister v_3242;
      setRegister (lhs.of_reg v_3243) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6444 0 64) 53 11) (MInt2Float (extract v_6447 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6444 64 128) 53 11) (MInt2Float (extract v_6447 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3239 : Mem) (v_3238 : reg (bv 128)) => do
      v_9288 <- getRegister v_3238;
      v_9291 <- evaluateAddress v_3239;
      v_9292 <- load v_9291 16;
      setRegister (lhs.of_reg v_3238) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9288 0 64) 53 11) (MInt2Float (extract v_9292 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9288 64 128) 53 11) (MInt2Float (extract v_9292 64 128) 53 11)) 64));
      pure ()
    pat_end

def divpd1 : instruction :=
  definst "divpd" $ do
    pattern fun (v_2725 : reg (bv 128)) (v_2726 : reg (bv 128)) => do
      v_4529 <- getRegister v_2726;
      v_4532 <- getRegister v_2725;
      setRegister (lhs.of_reg v_2726) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4529 0 64) 53 11) (MInt2Float (extract v_4532 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4529 64 128) 53 11) (MInt2Float (extract v_4532 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2721 : Mem) (v_2722 : reg (bv 128)) => do
      v_8274 <- getRegister v_2722;
      v_8277 <- evaluateAddress v_2721;
      v_8278 <- load v_8277 16;
      setRegister (lhs.of_reg v_2722) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8274 0 64) 53 11) (MInt2Float (extract v_8278 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8274 64 128) 53 11) (MInt2Float (extract v_8278 64 128) 53 11)) 64));
      pure ()
    pat_end

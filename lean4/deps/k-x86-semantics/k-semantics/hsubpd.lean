def hsubpd1 : instruction :=
  definst "hsubpd" $ do
    pattern fun (v_2832 : reg (bv 128)) (v_2833 : reg (bv 128)) => do
      v_4845 <- getRegister v_2832;
      v_4852 <- getRegister v_2833;
      setRegister (lhs.of_reg v_2833) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4845 64 128) 53 11) (MInt2Float (extract v_4845 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4852 64 128) 53 11) (MInt2Float (extract v_4852 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2828 : Mem) (v_2829 : reg (bv 128)) => do
      v_8531 <- evaluateAddress v_2828;
      v_8532 <- load v_8531 16;
      v_8539 <- getRegister v_2829;
      setRegister (lhs.of_reg v_2829) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8532 64 128) 53 11) (MInt2Float (extract v_8532 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8539 64 128) 53 11) (MInt2Float (extract v_8539 0 64) 53 11)) 64));
      pure ()
    pat_end

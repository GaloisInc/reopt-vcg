def divsd1 : instruction :=
  definst "divsd" $ do
    pattern fun (v_2750 : reg (bv 128)) (v_2751 : reg (bv 128)) => do
      v_4600 <- getRegister v_2751;
      v_4604 <- getRegister v_2750;
      setRegister (lhs.of_reg v_2751) (concat (extract v_4600 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4600 64 128) 53 11) (MInt2Float (extract v_4604 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2746 : Mem) (v_2747 : reg (bv 128)) => do
      v_8337 <- getRegister v_2747;
      v_8341 <- evaluateAddress v_2746;
      v_8342 <- load v_8341 8;
      setRegister (lhs.of_reg v_2747) (concat (extract v_8337 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8337 64 128) 53 11) (MInt2Float v_8342 53 11)) 64));
      pure ()
    pat_end

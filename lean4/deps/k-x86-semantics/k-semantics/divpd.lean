def divpd1 : instruction :=
  definst "divpd" $ do
    pattern fun (v_2816 : reg (bv 128)) (v_2817 : reg (bv 128)) => do
      v_4543 <- getRegister v_2817;
      v_4546 <- getRegister v_2816;
      setRegister (lhs.of_reg v_2817) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4543 0 64) 53 11) (MInt2Float (extract v_4546 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4543 64 128) 53 11) (MInt2Float (extract v_4546 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2812 : Mem) (v_2813 : reg (bv 128)) => do
      v_8062 <- getRegister v_2813;
      v_8065 <- evaluateAddress v_2812;
      v_8066 <- load v_8065 16;
      setRegister (lhs.of_reg v_2813) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8062 0 64) 53 11) (MInt2Float (extract v_8066 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8062 64 128) 53 11) (MInt2Float (extract v_8066 64 128) 53 11)) 64));
      pure ()
    pat_end

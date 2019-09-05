def haddps1 : instruction :=
  definst "haddps" $ do
    pattern fun (v_2888 : reg (bv 128)) (v_2889 : reg (bv 128)) => do
      v_4788 <- getRegister v_2888;
      v_4802 <- getRegister v_2889;
      setRegister (lhs.of_reg v_2889) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4788 32 64) 24 8) (MInt2Float (extract v_4788 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4788 96 128) 24 8) (MInt2Float (extract v_4788 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4802 32 64) 24 8) (MInt2Float (extract v_4802 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4802 96 128) 24 8) (MInt2Float (extract v_4802 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2883 : Mem) (v_2884 : reg (bv 128)) => do
      v_8266 <- evaluateAddress v_2883;
      v_8267 <- load v_8266 16;
      v_8281 <- getRegister v_2884;
      setRegister (lhs.of_reg v_2884) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8267 32 64) 24 8) (MInt2Float (extract v_8267 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8267 96 128) 24 8) (MInt2Float (extract v_8267 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8281 32 64) 24 8) (MInt2Float (extract v_8281 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8281 96 128) 24 8) (MInt2Float (extract v_8281 64 96) 24 8)) 32));
      pure ()
    pat_end

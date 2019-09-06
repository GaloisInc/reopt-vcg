def haddpd1 : instruction :=
  definst "haddpd" $ do
    pattern fun (v_2905 : reg (bv 128)) (v_2906 : reg (bv 128)) => do
      v_4789 <- getRegister v_2905;
      v_4796 <- getRegister v_2906;
      setRegister (lhs.of_reg v_2906) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4789 64 128) 53 11) (MInt2Float (extract v_4789 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4796 64 128) 53 11) (MInt2Float (extract v_4796 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2901 : Mem) (v_2902 : reg (bv 128)) => do
      v_8259 <- evaluateAddress v_2901;
      v_8260 <- load v_8259 16;
      v_8267 <- getRegister v_2902;
      setRegister (lhs.of_reg v_2902) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8260 64 128) 53 11) (MInt2Float (extract v_8260 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8267 64 128) 53 11) (MInt2Float (extract v_8267 0 64) 53 11)) 64));
      pure ()
    pat_end

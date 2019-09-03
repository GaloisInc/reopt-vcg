def haddps1 : instruction :=
  definst "haddps" $ do
    pattern fun (v_2823 : reg (bv 128)) (v_2824 : reg (bv 128)) => do
      v_4811 <- getRegister v_2823;
      v_4825 <- getRegister v_2824;
      setRegister (lhs.of_reg v_2824) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4811 32 64) 24 8) (MInt2Float (extract v_4811 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4811 96 128) 24 8) (MInt2Float (extract v_4811 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4825 32 64) 24 8) (MInt2Float (extract v_4825 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4825 96 128) 24 8) (MInt2Float (extract v_4825 64 96) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2819 : Mem) (v_2820 : reg (bv 128)) => do
      v_8500 <- evaluateAddress v_2819;
      v_8501 <- load v_8500 16;
      v_8515 <- getRegister v_2820;
      setRegister (lhs.of_reg v_2820) (concat (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8501 32 64) 24 8) (MInt2Float (extract v_8501 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8501 96 128) 24 8) (MInt2Float (extract v_8501 64 96) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8515 32 64) 24 8) (MInt2Float (extract v_8515 0 32) 24 8)) 32)) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8515 96 128) 24 8) (MInt2Float (extract v_8515 64 96) 24 8)) 32));
      pure ()
    pat_end

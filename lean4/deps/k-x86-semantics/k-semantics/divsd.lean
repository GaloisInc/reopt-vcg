def divsd1 : instruction :=
  definst "divsd" $ do
    pattern fun (v_2815 : reg (bv 128)) (v_2816 : reg (bv 128)) => do
      v_4593 <- getRegister v_2816;
      v_4597 <- getRegister v_2815;
      setRegister (lhs.of_reg v_2816) (concat (extract v_4593 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4593 64 128) 53 11) (MInt2Float (extract v_4597 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2810 : Mem) (v_2811 : reg (bv 128)) => do
      v_8115 <- getRegister v_2811;
      v_8119 <- evaluateAddress v_2810;
      v_8120 <- load v_8119 8;
      setRegister (lhs.of_reg v_2811) (concat (extract v_8115 0 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8115 64 128) 53 11) (MInt2Float v_8120 53 11)) 64));
      pure ()
    pat_end

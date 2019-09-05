def divss1 : instruction :=
  definst "divss" $ do
    pattern fun (v_2824 : reg (bv 128)) (v_2825 : reg (bv 128)) => do
      v_4608 <- getRegister v_2825;
      v_4612 <- getRegister v_2824;
      setRegister (lhs.of_reg v_2825) (concat (extract v_4608 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4608 96 128) 24 8) (MInt2Float (extract v_4612 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2819 : Mem) (v_2820 : reg (bv 128)) => do
      v_8126 <- getRegister v_2820;
      v_8130 <- evaluateAddress v_2819;
      v_8131 <- load v_8130 4;
      setRegister (lhs.of_reg v_2820) (concat (extract v_8126 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8126 96 128) 24 8) (MInt2Float v_8131 24 8)) 32));
      pure ()
    pat_end

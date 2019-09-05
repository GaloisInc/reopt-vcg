def mulss1 : instruction :=
  definst "mulss" $ do
    pattern fun (v_2825 : reg (bv 128)) (v_2826 : reg (bv 128)) => do
      v_4314 <- getRegister v_2826;
      v_4318 <- getRegister v_2825;
      setRegister (lhs.of_reg v_2826) (concat (extract v_4314 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_4314 96 128) 24 8) (MInt2Float (extract v_4318 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2820 : Mem) (v_2821 : reg (bv 128)) => do
      v_8873 <- getRegister v_2821;
      v_8877 <- evaluateAddress v_2820;
      v_8878 <- load v_8877 4;
      setRegister (lhs.of_reg v_2821) (concat (extract v_8873 0 96) (Float2MInt (_*Float__FLOAT (MInt2Float (extract v_8873 96 128) 24 8) (MInt2Float v_8878 24 8)) 32));
      pure ()
    pat_end

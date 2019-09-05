def cvtsi2ssq1 : instruction :=
  definst "cvtsi2ssq" $ do
    pattern fun (v_2643 : reg (bv 64)) (v_2645 : reg (bv 128)) => do
      v_4254 <- getRegister v_2645;
      v_4256 <- getRegister v_2643;
      setRegister (lhs.of_reg v_2645) (concat (extract v_4254 0 96) (Float2MInt (Int2Float (svalueMInt v_4256) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2639 : Mem) (v_2640 : reg (bv 128)) => do
      v_7950 <- getRegister v_2640;
      v_7952 <- evaluateAddress v_2639;
      v_7953 <- load v_7952 8;
      setRegister (lhs.of_reg v_2640) (concat (extract v_7950 0 96) (Float2MInt (Int2Float (svalueMInt v_7953) 24 8) 32));
      pure ()
    pat_end

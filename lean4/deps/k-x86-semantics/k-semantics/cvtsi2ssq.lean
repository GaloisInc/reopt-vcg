def cvtsi2ssq1 : instruction :=
  definst "cvtsi2ssq" $ do
    pattern fun (v_2579 : reg (bv 64)) (v_2580 : reg (bv 128)) => do
      v_4244 <- getRegister v_2580;
      v_4246 <- getRegister v_2579;
      setRegister (lhs.of_reg v_2580) (concat (extract v_4244 0 96) (Float2MInt (Int2Float (svalueMInt v_4246) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2575 : Mem) (v_2576 : reg (bv 128)) => do
      v_8172 <- getRegister v_2576;
      v_8174 <- evaluateAddress v_2575;
      v_8175 <- load v_8174 8;
      setRegister (lhs.of_reg v_2576) (concat (extract v_8172 0 96) (Float2MInt (Int2Float (svalueMInt v_8175) 24 8) 32));
      pure ()
    pat_end

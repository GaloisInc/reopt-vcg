def cvtsi2ssl1 : instruction :=
  definst "cvtsi2ssl" $ do
    pattern fun (v_2661 : reg (bv 32)) (v_2662 : reg (bv 128)) => do
      v_4263 <- getRegister v_2662;
      v_4265 <- getRegister v_2661;
      setRegister (lhs.of_reg v_2662) (concat (extract v_4263 0 96) (Float2MInt (Int2Float (svalueMInt v_4265) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2657 : Mem) (v_2658 : reg (bv 128)) => do
      v_7951 <- getRegister v_2658;
      v_7953 <- evaluateAddress v_2657;
      v_7954 <- load v_7953 4;
      setRegister (lhs.of_reg v_2658) (concat (extract v_7951 0 96) (Float2MInt (Int2Float (svalueMInt v_7954) 24 8) 32));
      pure ()
    pat_end

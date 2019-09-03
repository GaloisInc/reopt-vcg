def cvtsi2ssl1 : instruction :=
  definst "cvtsi2ssl" $ do
    pattern fun (v_2571 : reg (bv 32)) (v_2570 : reg (bv 128)) => do
      v_4232 <- getRegister v_2570;
      v_4234 <- getRegister v_2571;
      setRegister (lhs.of_reg v_2570) (concat (extract v_4232 0 96) (Float2MInt (Int2Float (svalueMInt v_4234) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2566 : Mem) (v_2567 : reg (bv 128)) => do
      v_8163 <- getRegister v_2567;
      v_8165 <- evaluateAddress v_2566;
      v_8166 <- load v_8165 4;
      setRegister (lhs.of_reg v_2567) (concat (extract v_8163 0 96) (Float2MInt (Int2Float (svalueMInt v_8166) 24 8) 32));
      pure ()
    pat_end

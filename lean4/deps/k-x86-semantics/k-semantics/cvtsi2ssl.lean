def cvtsi2ssl1 : instruction :=
  definst "cvtsi2ssl" $ do
    pattern fun (v_2635 : reg (bv 32)) (v_2636 : reg (bv 128)) => do
      v_4242 <- getRegister v_2636;
      v_4244 <- getRegister v_2635;
      setRegister (lhs.of_reg v_2636) (concat (extract v_4242 0 96) (Float2MInt (Int2Float (svalueMInt v_4244) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2630 : Mem) (v_2631 : reg (bv 128)) => do
      v_7941 <- getRegister v_2631;
      v_7943 <- evaluateAddress v_2630;
      v_7944 <- load v_7943 4;
      setRegister (lhs.of_reg v_2631) (concat (extract v_7941 0 96) (Float2MInt (Int2Float (svalueMInt v_7944) 24 8) 32));
      pure ()
    pat_end

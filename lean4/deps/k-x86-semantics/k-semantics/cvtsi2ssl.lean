def cvtsi2ssl1 : instruction :=
  definst "cvtsi2ssl" $ do
    pattern fun (v_2582 : reg (bv 32)) (v_2584 : reg (bv 128)) => do
      v_4248 <- getRegister v_2584;
      v_4250 <- getRegister v_2582;
      setRegister (lhs.of_reg v_2584) (concat (extract v_4248 0 96) (Float2MInt (Int2Float (svalueMInt v_4250) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2577 : Mem) (v_2579 : reg (bv 128)) => do
      v_8465 <- getRegister v_2579;
      v_8467 <- evaluateAddress v_2577;
      v_8468 <- load v_8467 4;
      setRegister (lhs.of_reg v_2579) (concat (extract v_8465 0 96) (Float2MInt (Int2Float (svalueMInt v_8468) 24 8) 32));
      pure ()
    pat_end

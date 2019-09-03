def cvtsi2sdq1 : instruction :=
  definst "cvtsi2sdq" $ do
    pattern fun (v_2573 : reg (bv 64)) (v_2575 : reg (bv 128)) => do
      v_4236 <- getRegister v_2575;
      v_4238 <- getRegister v_2573;
      setRegister (lhs.of_reg v_2575) (concat (extract v_4236 0 64) (Float2MInt (Int2Float (svalueMInt v_4238) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2568 : Mem) (v_2570 : reg (bv 128)) => do
      v_8456 <- getRegister v_2570;
      v_8458 <- evaluateAddress v_2568;
      v_8459 <- load v_8458 8;
      setRegister (lhs.of_reg v_2570) (concat (extract v_8456 0 64) (Float2MInt (Int2Float (svalueMInt v_8459) 53 11) 64));
      pure ()
    pat_end

def pmuldq1 : instruction :=
  definst "pmuldq" $ do
    pattern fun (v_2774 : reg (bv 128)) (v_2775 : reg (bv 128)) => do
      v_5682 <- getRegister v_2775;
      v_5686 <- getRegister v_2774;
      setRegister (lhs.of_reg v_2775) (concat (mul (mi 64 (svalueMInt (extract v_5682 32 64))) (mi 64 (svalueMInt (extract v_5686 32 64)))) (mul (mi 64 (svalueMInt (extract v_5682 96 128))) (mi 64 (svalueMInt (extract v_5686 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_2769 : Mem) (v_2770 : reg (bv 128)) => do
      v_12945 <- getRegister v_2770;
      v_12949 <- evaluateAddress v_2769;
      v_12950 <- load v_12949 16;
      setRegister (lhs.of_reg v_2770) (concat (mul (mi 64 (svalueMInt (extract v_12945 32 64))) (mi 64 (svalueMInt (extract v_12950 32 64)))) (mul (mi 64 (svalueMInt (extract v_12945 96 128))) (mi 64 (svalueMInt (extract v_12950 96 128)))));
      pure ()
    pat_end

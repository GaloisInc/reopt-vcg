def pmovsxbd1 : instruction :=
  definst "pmovsxbd" $ do
    pattern fun (v_2666 : reg (bv 128)) (v_2667 : reg (bv 128)) => do
      v_5468 <- getRegister v_2666;
      setRegister (lhs.of_reg v_2667) (concat (mi 32 (svalueMInt (extract v_5468 96 104))) (concat (mi 32 (svalueMInt (extract v_5468 104 112))) (concat (mi 32 (svalueMInt (extract v_5468 112 120))) (mi 32 (svalueMInt (extract v_5468 120 128))))));
      pure ()
    pat_end;
    pattern fun (v_2661 : Mem) (v_2662 : reg (bv 128)) => do
      v_12767 <- evaluateAddress v_2661;
      v_12768 <- load v_12767 4;
      setRegister (lhs.of_reg v_2662) (concat (mi 32 (svalueMInt (extract v_12768 0 8))) (concat (mi 32 (svalueMInt (extract v_12768 8 16))) (concat (mi 32 (svalueMInt (extract v_12768 16 24))) (mi 32 (svalueMInt (extract v_12768 24 32))))));
      pure ()
    pat_end

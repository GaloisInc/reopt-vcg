def vpmovsxbd1 : instruction :=
  definst "vpmovsxbd" $ do
    pattern fun (v_2591 : reg (bv 128)) (v_2592 : reg (bv 128)) => do
      v_5404 <- getRegister v_2591;
      setRegister (lhs.of_reg v_2592) (concat (mi 32 (svalueMInt (extract v_5404 96 104))) (concat (mi 32 (svalueMInt (extract v_5404 104 112))) (concat (mi 32 (svalueMInt (extract v_5404 112 120))) (mi 32 (svalueMInt (extract v_5404 120 128))))));
      pure ()
    pat_end;
    pattern fun (v_2600 : reg (bv 128)) (v_2601 : reg (bv 256)) => do
      v_5425 <- getRegister v_2600;
      setRegister (lhs.of_reg v_2601) (concat (mi 32 (svalueMInt (extract v_5425 64 72))) (concat (mi 32 (svalueMInt (extract v_5425 72 80))) (concat (mi 32 (svalueMInt (extract v_5425 80 88))) (concat (mi 32 (svalueMInt (extract v_5425 88 96))) (concat (mi 32 (svalueMInt (extract v_5425 96 104))) (concat (mi 32 (svalueMInt (extract v_5425 104 112))) (concat (mi 32 (svalueMInt (extract v_5425 112 120))) (mi 32 (svalueMInt (extract v_5425 120 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_2588 : Mem) (v_2587 : reg (bv 128)) => do
      v_12582 <- evaluateAddress v_2588;
      v_12583 <- load v_12582 4;
      setRegister (lhs.of_reg v_2587) (concat (mi 32 (svalueMInt (extract v_12583 0 8))) (concat (mi 32 (svalueMInt (extract v_12583 8 16))) (concat (mi 32 (svalueMInt (extract v_12583 16 24))) (mi 32 (svalueMInt (extract v_12583 24 32))))));
      pure ()
    pat_end;
    pattern fun (v_2596 : Mem) (v_2597 : reg (bv 256)) => do
      v_12600 <- evaluateAddress v_2596;
      v_12601 <- load v_12600 8;
      setRegister (lhs.of_reg v_2597) (concat (mi 32 (svalueMInt (extract v_12601 0 8))) (concat (mi 32 (svalueMInt (extract v_12601 8 16))) (concat (mi 32 (svalueMInt (extract v_12601 16 24))) (concat (mi 32 (svalueMInt (extract v_12601 24 32))) (concat (mi 32 (svalueMInt (extract v_12601 32 40))) (concat (mi 32 (svalueMInt (extract v_12601 40 48))) (concat (mi 32 (svalueMInt (extract v_12601 48 56))) (mi 32 (svalueMInt (extract v_12601 56 64))))))))));
      pure ()
    pat_end

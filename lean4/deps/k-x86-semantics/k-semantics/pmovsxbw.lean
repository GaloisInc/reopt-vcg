def pmovsxbw1 : instruction :=
  definst "pmovsxbw" $ do
    pattern fun (v_2684 : reg (bv 128)) (v_2685 : reg (bv 128)) => do
      v_5502 <- getRegister v_2684;
      setRegister (lhs.of_reg v_2685) (concat (mi 16 (svalueMInt (extract v_5502 64 72))) (concat (mi 16 (svalueMInt (extract v_5502 72 80))) (concat (mi 16 (svalueMInt (extract v_5502 80 88))) (concat (mi 16 (svalueMInt (extract v_5502 88 96))) (concat (mi 16 (svalueMInt (extract v_5502 96 104))) (concat (mi 16 (svalueMInt (extract v_5502 104 112))) (concat (mi 16 (svalueMInt (extract v_5502 112 120))) (mi 16 (svalueMInt (extract v_5502 120 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_2679 : Mem) (v_2680 : reg (bv 128)) => do
      v_12795 <- evaluateAddress v_2679;
      v_12796 <- load v_12795 8;
      setRegister (lhs.of_reg v_2680) (concat (mi 16 (svalueMInt (extract v_12796 0 8))) (concat (mi 16 (svalueMInt (extract v_12796 8 16))) (concat (mi 16 (svalueMInt (extract v_12796 16 24))) (concat (mi 16 (svalueMInt (extract v_12796 24 32))) (concat (mi 16 (svalueMInt (extract v_12796 32 40))) (concat (mi 16 (svalueMInt (extract v_12796 40 48))) (concat (mi 16 (svalueMInt (extract v_12796 48 56))) (mi 16 (svalueMInt (extract v_12796 56 64))))))))));
      pure ()
    pat_end

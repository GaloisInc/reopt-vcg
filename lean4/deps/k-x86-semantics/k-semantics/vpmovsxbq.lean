def vpmovsxbq1 : instruction :=
  definst "vpmovsxbq" $ do
    pattern fun (v_2609 : reg (bv 128)) (v_2610 : reg (bv 128)) => do
      v_5462 <- getRegister v_2609;
      setRegister (lhs.of_reg v_2610) (concat (mi 64 (svalueMInt (extract v_5462 112 120))) (mi 64 (svalueMInt (extract v_5462 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2618 : reg (bv 128)) (v_2619 : reg (bv 256)) => do
      v_5475 <- getRegister v_2618;
      setRegister (lhs.of_reg v_2619) (concat (mi 64 (svalueMInt (extract v_5475 96 104))) (concat (mi 64 (svalueMInt (extract v_5475 104 112))) (concat (mi 64 (svalueMInt (extract v_5475 112 120))) (mi 64 (svalueMInt (extract v_5475 120 128))))));
      pure ()
    pat_end;
    pattern fun (v_2606 : Mem) (v_2605 : reg (bv 128)) => do
      v_12634 <- evaluateAddress v_2606;
      v_12635 <- load v_12634 2;
      setRegister (lhs.of_reg v_2605) (concat (mi 64 (svalueMInt (extract v_12635 0 8))) (mi 64 (svalueMInt (extract v_12635 8 16))));
      pure ()
    pat_end;
    pattern fun (v_2614 : Mem) (v_2615 : reg (bv 256)) => do
      v_12644 <- evaluateAddress v_2614;
      v_12645 <- load v_12644 4;
      setRegister (lhs.of_reg v_2615) (concat (mi 64 (svalueMInt (extract v_12645 0 8))) (concat (mi 64 (svalueMInt (extract v_12645 8 16))) (concat (mi 64 (svalueMInt (extract v_12645 16 24))) (mi 64 (svalueMInt (extract v_12645 24 32))))));
      pure ()
    pat_end

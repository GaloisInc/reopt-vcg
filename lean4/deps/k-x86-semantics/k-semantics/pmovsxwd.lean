def pmovsxwd1 : instruction :=
  definst "pmovsxwd" $ do
    pattern fun (v_2702 : reg (bv 128)) (v_2703 : reg (bv 128)) => do
      v_5552 <- getRegister v_2702;
      setRegister (lhs.of_reg v_2703) (concat (mi 32 (svalueMInt (extract v_5552 64 80))) (concat (mi 32 (svalueMInt (extract v_5552 80 96))) (concat (mi 32 (svalueMInt (extract v_5552 96 112))) (mi 32 (svalueMInt (extract v_5552 112 128))))));
      pure ()
    pat_end;
    pattern fun (v_2697 : Mem) (v_2698 : reg (bv 128)) => do
      v_12839 <- evaluateAddress v_2697;
      v_12840 <- load v_12839 8;
      setRegister (lhs.of_reg v_2698) (concat (mi 32 (svalueMInt (extract v_12840 0 16))) (concat (mi 32 (svalueMInt (extract v_12840 16 32))) (concat (mi 32 (svalueMInt (extract v_12840 32 48))) (mi 32 (svalueMInt (extract v_12840 48 64))))));
      pure ()
    pat_end

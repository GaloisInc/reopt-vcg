def pmovsxbq1 : instruction :=
  definst "pmovsxbq" $ do
    pattern fun (v_2675 : reg (bv 128)) (v_2676 : reg (bv 128)) => do
      v_5489 <- getRegister v_2675;
      setRegister (lhs.of_reg v_2676) (concat (mi 64 (svalueMInt (extract v_5489 112 120))) (mi 64 (svalueMInt (extract v_5489 120 128))));
      pure ()
    pat_end;
    pattern fun (v_2670 : Mem) (v_2671 : reg (bv 128)) => do
      v_12785 <- evaluateAddress v_2670;
      v_12786 <- load v_12785 2;
      setRegister (lhs.of_reg v_2671) (concat (mi 64 (svalueMInt (extract v_12786 0 8))) (mi 64 (svalueMInt (extract v_12786 8 16))));
      pure ()
    pat_end

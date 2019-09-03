def movzbq1 : instruction :=
  definst "movzbq" $ do
    pattern fun (v_2681 : reg (bv 8)) (v_2682 : reg (bv 64)) => do
      v_4083 <- getRegister v_2681;
      setRegister (lhs.of_reg v_2682) (concat (expression.bv_nat 56 0) v_4083);
      pure ()
    pat_end;
    pattern fun (v_2677 : Mem) (v_2678 : reg (bv 64)) => do
      v_8878 <- evaluateAddress v_2677;
      v_8879 <- load v_8878 1;
      setRegister (lhs.of_reg v_2678) (concat (expression.bv_nat 56 0) v_8879);
      pure ()
    pat_end

def movzbq1 : instruction :=
  definst "movzbq" $ do
    pattern fun (v_2758 : reg (bv 8)) (v_2757 : reg (bv 64)) => do
      v_4161 <- getRegister v_2758;
      setRegister (lhs.of_reg v_2757) (concat (expression.bv_nat 56 0) v_4161);
      pure ()
    pat_end;
    pattern fun (v_2753 : Mem) (v_2754 : reg (bv 64)) => do
      v_8769 <- evaluateAddress v_2753;
      v_8770 <- load v_8769 1;
      setRegister (lhs.of_reg v_2754) (concat (expression.bv_nat 56 0) v_8770);
      pure ()
    pat_end

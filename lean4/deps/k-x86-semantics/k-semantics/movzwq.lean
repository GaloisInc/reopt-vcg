def movzwq1 : instruction :=
  definst "movzwq" $ do
    pattern fun (v_2713 : reg (bv 16)) (v_2714 : reg (bv 64)) => do
      v_4107 <- getRegister v_2713;
      setRegister (lhs.of_reg v_2714) (concat (expression.bv_nat 48 0) v_4107);
      pure ()
    pat_end;
    pattern fun (v_2709 : Mem) (v_2710 : reg (bv 64)) => do
      v_8890 <- evaluateAddress v_2709;
      v_8891 <- load v_8890 2;
      setRegister (lhs.of_reg v_2710) (concat (expression.bv_nat 48 0) v_8891);
      pure ()
    pat_end

def movzbl1 : instruction :=
  definst "movzbl" $ do
    pattern fun (v_2722 : reg (bv 8)) (v_2724 : reg (bv 32)) => do
      v_4127 <- getRegister v_2722;
      setRegister (lhs.of_reg v_2724) (concat (expression.bv_nat 24 0) v_4127);
      pure ()
    pat_end;
    pattern fun (v_2713 : Mem) (v_2714 : reg (bv 32)) => do
      v_8738 <- evaluateAddress v_2713;
      v_8739 <- load v_8738 1;
      setRegister (lhs.of_reg v_2714) (concat (expression.bv_nat 24 0) v_8739);
      pure ()
    pat_end

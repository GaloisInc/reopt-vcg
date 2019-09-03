def movzbl1 : instruction :=
  definst "movzbl" $ do
    pattern fun (v_2655 : reg (bv 8)) (v_2656 : reg (bv 32)) => do
      v_4060 <- getRegister v_2655;
      setRegister (lhs.of_reg v_2656) (concat (expression.bv_nat 24 0) v_4060);
      pure ()
    pat_end;
    pattern fun (v_2650 : Mem) (v_2651 : reg (bv 32)) => do
      v_8895 <- evaluateAddress v_2650;
      v_8896 <- load v_8895 1;
      setRegister (lhs.of_reg v_2651) (concat (expression.bv_nat 24 0) v_8896);
      pure ()
    pat_end

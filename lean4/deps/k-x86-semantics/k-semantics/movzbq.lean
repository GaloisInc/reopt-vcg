def movzbq1 : instruction :=
  definst "movzbq" $ do
    pattern fun (v_2731 : reg (bv 8)) (v_2732 : reg (bv 64)) => do
      v_4134 <- getRegister v_2731;
      setRegister (lhs.of_reg v_2732) (concat (expression.bv_nat 56 0) v_4134);
      pure ()
    pat_end;
    pattern fun (v_2727 : Mem) (v_2728 : reg (bv 64)) => do
      v_8742 <- evaluateAddress v_2727;
      v_8743 <- load v_8742 1;
      setRegister (lhs.of_reg v_2728) (concat (expression.bv_nat 56 0) v_8743);
      pure ()
    pat_end

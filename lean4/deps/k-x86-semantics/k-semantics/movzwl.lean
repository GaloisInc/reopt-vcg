def movzwl1 : instruction :=
  definst "movzwl" $ do
    pattern fun (v_2755 : reg (bv 16)) (v_2756 : reg (bv 32)) => do
      v_4151 <- getRegister v_2755;
      setRegister (lhs.of_reg v_2756) (concat (expression.bv_nat 16 0) v_4151);
      pure ()
    pat_end;
    pattern fun (v_2750 : Mem) (v_2751 : reg (bv 32)) => do
      v_8750 <- evaluateAddress v_2750;
      v_8751 <- load v_8750 2;
      setRegister (lhs.of_reg v_2751) (concat (expression.bv_nat 16 0) v_8751);
      pure ()
    pat_end

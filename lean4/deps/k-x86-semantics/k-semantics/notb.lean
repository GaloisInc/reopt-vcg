def notb1 : instruction :=
  definst "notb" $ do
    pattern fun (v_2931 : reg (bv 8)) => do
      v_4524 <- getRegister v_2931;
      setRegister (lhs.of_reg v_2931) (bv_xor v_4524 (expression.bv_nat 8 255));
      pure ()
    pat_end;
    pattern fun (v_2924 : Mem) => do
      v_10785 <- evaluateAddress v_2924;
      v_10786 <- load v_10785 1;
      store v_10785 (bv_xor v_10786 (expression.bv_nat 8 255)) 1;
      pure ()
    pat_end

def notb1 : instruction :=
  definst "notb" $ do
    pattern fun (v_2877 : reg (bv 8)) => do
      v_4606 <- getRegister v_2877;
      setRegister (lhs.of_reg v_2877) (bv_xor v_4606 (expression.bv_nat 8 255));
      pure ()
    pat_end;
    pattern fun (v_2874 : Mem) => do
      v_11098 <- evaluateAddress v_2874;
      v_11099 <- load v_11098 1;
      store v_11098 (bv_xor v_11099 (expression.bv_nat 8 255)) 1;
      pure ()
    pat_end

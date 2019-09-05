def notl1 : instruction :=
  definst "notl" $ do
    pattern fun (v_2939 : reg (bv 32)) => do
      v_4530 <- getRegister v_2939;
      setRegister (lhs.of_reg v_2939) (bv_xor v_4530 (expression.bv_nat 32 4294967295));
      pure ()
    pat_end;
    pattern fun (v_2935 : Mem) => do
      v_10789 <- evaluateAddress v_2935;
      v_10790 <- load v_10789 4;
      store v_10789 (bv_xor v_10790 (expression.bv_nat 32 4294967295)) 4;
      pure ()
    pat_end

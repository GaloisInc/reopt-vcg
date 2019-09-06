def notq1 : instruction :=
  definst "notq" $ do
    pattern fun (v_2971 : reg (bv 64)) => do
      v_4563 <- getRegister v_2971;
      setRegister (lhs.of_reg v_2971) (bv_xor v_4563 (expression.bv_nat 64 18446744073709551615));
      pure ()
    pat_end;
    pattern fun (v_2968 : Mem) => do
      v_10820 <- evaluateAddress v_2968;
      v_10821 <- load v_10820 8;
      store v_10820 (bv_xor v_10821 (expression.bv_nat 64 18446744073709551615)) 8;
      pure ()
    pat_end

def notq1 : instruction :=
  definst "notq" $ do
    pattern fun (v_2895 : reg (bv 64)) => do
      v_4621 <- getRegister v_2895;
      setRegister (lhs.of_reg v_2895) (bv_xor v_4621 (expression.bv_nat 64 18446744073709551615));
      pure ()
    pat_end;
    pattern fun (v_2892 : Mem) => do
      v_11106 <- evaluateAddress v_2892;
      v_11107 <- load v_11106 8;
      store v_11106 (bv_xor v_11107 (expression.bv_nat 64 18446744073709551615)) 8;
      pure ()
    pat_end

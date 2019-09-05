def notq1 : instruction :=
  definst "notq" $ do
    pattern fun (v_2945 : reg (bv 64)) => do
      v_4536 <- getRegister v_2945;
      setRegister (lhs.of_reg v_2945) (bv_xor v_4536 (expression.bv_nat 64 18446744073709551615));
      pure ()
    pat_end;
    pattern fun (v_2942 : Mem) => do
      v_10793 <- evaluateAddress v_2942;
      v_10794 <- load v_10793 8;
      store v_10793 (bv_xor v_10794 (expression.bv_nat 64 18446744073709551615)) 8;
      pure ()
    pat_end

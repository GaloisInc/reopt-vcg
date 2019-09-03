def cmovnbew1 : instruction :=
  definst "cmovnbew" $ do
    pattern fun (v_2788 : reg (bv 16)) (v_2789 : reg (bv 16)) => do
      v_4560 <- getRegister cf;
      v_4563 <- getRegister zf;
      v_4567 <- getRegister v_2788;
      v_4568 <- getRegister v_2789;
      setRegister (lhs.of_reg v_2789) (mux (bit_and (notBool_ (eq v_4560 (expression.bv_nat 1 1))) (notBool_ (eq v_4563 (expression.bv_nat 1 1)))) v_4567 v_4568);
      pure ()
    pat_end;
    pattern fun (v_2785 : Mem) (v_2784 : reg (bv 16)) => do
      v_8184 <- getRegister cf;
      v_8187 <- getRegister zf;
      v_8191 <- evaluateAddress v_2785;
      v_8192 <- load v_8191 2;
      v_8193 <- getRegister v_2784;
      setRegister (lhs.of_reg v_2784) (mux (bit_and (notBool_ (eq v_8184 (expression.bv_nat 1 1))) (notBool_ (eq v_8187 (expression.bv_nat 1 1)))) v_8192 v_8193);
      pure ()
    pat_end

def cmovnbq1 : instruction :=
  definst "cmovnbq" $ do
    pattern fun (v_2870 : reg (bv 64)) (v_2871 : reg (bv 64)) => do
      v_4650 <- getRegister cf;
      v_4653 <- getRegister v_2870;
      v_4654 <- getRegister v_2871;
      setRegister (lhs.of_reg v_2871) (mux (notBool_ (eq v_4650 (expression.bv_nat 1 1))) v_4653 v_4654);
      pure ()
    pat_end;
    pattern fun (v_2865 : Mem) (v_2866 : reg (bv 64)) => do
      v_8190 <- getRegister cf;
      v_8193 <- evaluateAddress v_2865;
      v_8194 <- load v_8193 8;
      v_8195 <- getRegister v_2866;
      setRegister (lhs.of_reg v_2866) (mux (notBool_ (eq v_8190 (expression.bv_nat 1 1))) v_8194 v_8195);
      pure ()
    pat_end

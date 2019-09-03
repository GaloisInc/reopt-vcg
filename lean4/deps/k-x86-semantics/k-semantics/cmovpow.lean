def cmovpow1 : instruction :=
  definst "cmovpow" $ do
    pattern fun (v_3199 : reg (bv 16)) (v_3200 : reg (bv 16)) => do
      v_5096 <- getRegister pf;
      v_5099 <- getRegister v_3199;
      v_5100 <- getRegister v_3200;
      setRegister (lhs.of_reg v_3200) (mux (notBool_ (eq v_5096 (expression.bv_nat 1 1))) v_5099 v_5100);
      pure ()
    pat_end;
    pattern fun (v_3196 : Mem) (v_3195 : reg (bv 16)) => do
      v_8579 <- getRegister pf;
      v_8582 <- evaluateAddress v_3196;
      v_8583 <- load v_8582 2;
      v_8584 <- getRegister v_3195;
      setRegister (lhs.of_reg v_3195) (mux (notBool_ (eq v_8579 (expression.bv_nat 1 1))) v_8583 v_8584);
      pure ()
    pat_end

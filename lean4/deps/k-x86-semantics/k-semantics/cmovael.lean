def cmovael1 : instruction :=
  definst "cmovael" $ do
    pattern fun (v_3364 : reg (bv 32)) (v_3365 : reg (bv 32)) => do
      v_6697 <- getRegister cf;
      v_6699 <- getRegister v_3364;
      v_6700 <- getRegister v_3365;
      setRegister (lhs.of_reg v_3365) (mux (notBool_ v_6697) v_6699 v_6700);
      pure ()
    pat_end;
    pattern fun (v_3359 : Mem) (v_3360 : reg (bv 32)) => do
      v_9800 <- getRegister cf;
      v_9802 <- evaluateAddress v_3359;
      v_9803 <- load v_9802 4;
      v_9804 <- getRegister v_3360;
      setRegister (lhs.of_reg v_3360) (mux (notBool_ v_9800) v_9803 v_9804);
      pure ()
    pat_end

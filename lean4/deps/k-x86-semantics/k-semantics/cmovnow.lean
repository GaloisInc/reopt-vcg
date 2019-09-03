def cmovnow1 : instruction :=
  definst "cmovnow" $ do
    pattern fun (v_3004 : reg (bv 16)) (v_3005 : reg (bv 16)) => do
      v_4879 <- getRegister of;
      v_4882 <- getRegister v_3004;
      v_4883 <- getRegister v_3005;
      setRegister (lhs.of_reg v_3005) (mux (notBool_ (eq v_4879 (expression.bv_nat 1 1))) v_4882 v_4883);
      pure ()
    pat_end;
    pattern fun (v_3001 : Mem) (v_3000 : reg (bv 16)) => do
      v_8431 <- getRegister of;
      v_8434 <- evaluateAddress v_3001;
      v_8435 <- load v_8434 2;
      v_8436 <- getRegister v_3000;
      setRegister (lhs.of_reg v_3000) (mux (notBool_ (eq v_8431 (expression.bv_nat 1 1))) v_8435 v_8436);
      pure ()
    pat_end

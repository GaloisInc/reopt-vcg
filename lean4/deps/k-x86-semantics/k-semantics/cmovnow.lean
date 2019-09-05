def cmovnow1 : instruction :=
  definst "cmovnow" $ do
    pattern fun (v_3068 : reg (bv 16)) (v_3069 : reg (bv 16)) => do
      v_4943 <- getRegister of;
      v_4946 <- getRegister v_3068;
      v_4947 <- getRegister v_3069;
      setRegister (lhs.of_reg v_3069) (mux (notBool_ (eq v_4943 (expression.bv_nat 1 1))) v_4946 v_4947);
      pure ()
    pat_end;
    pattern fun (v_3063 : Mem) (v_3064 : reg (bv 16)) => do
      v_8417 <- getRegister of;
      v_8420 <- evaluateAddress v_3063;
      v_8421 <- load v_8420 2;
      v_8422 <- getRegister v_3064;
      setRegister (lhs.of_reg v_3064) (mux (notBool_ (eq v_8417 (expression.bv_nat 1 1))) v_8421 v_8422);
      pure ()
    pat_end

def cmovnow1 : instruction :=
  definst "cmovnow" $ do
    pattern fun (v_3018 : reg (bv 16)) (v_3019 : reg (bv 16)) => do
      v_4892 <- getRegister of;
      v_4895 <- getRegister v_3018;
      v_4896 <- getRegister v_3019;
      setRegister (lhs.of_reg v_3019) (mux (notBool_ (eq v_4892 (expression.bv_nat 1 1))) v_4895 v_4896);
      pure ()
    pat_end;
    pattern fun (v_3012 : Mem) (v_3014 : reg (bv 16)) => do
      v_8404 <- getRegister of;
      v_8407 <- evaluateAddress v_3012;
      v_8408 <- load v_8407 2;
      v_8409 <- getRegister v_3014;
      setRegister (lhs.of_reg v_3014) (mux (notBool_ (eq v_8404 (expression.bv_nat 1 1))) v_8408 v_8409);
      pure ()
    pat_end

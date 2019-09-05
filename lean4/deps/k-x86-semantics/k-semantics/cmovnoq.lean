def cmovnoq1 : instruction :=
  definst "cmovnoq" $ do
    pattern fun (v_3059 : reg (bv 64)) (v_3060 : reg (bv 64)) => do
      v_4932 <- getRegister of;
      v_4935 <- getRegister v_3059;
      v_4936 <- getRegister v_3060;
      setRegister (lhs.of_reg v_3060) (mux (notBool_ (eq v_4932 (expression.bv_nat 1 1))) v_4935 v_4936);
      pure ()
    pat_end;
    pattern fun (v_3054 : Mem) (v_3055 : reg (bv 64)) => do
      v_8409 <- getRegister of;
      v_8412 <- evaluateAddress v_3054;
      v_8413 <- load v_8412 8;
      v_8414 <- getRegister v_3055;
      setRegister (lhs.of_reg v_3055) (mux (notBool_ (eq v_8409 (expression.bv_nat 1 1))) v_8413 v_8414);
      pure ()
    pat_end

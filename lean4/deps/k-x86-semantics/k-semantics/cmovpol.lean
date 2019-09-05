def cmovpol1 : instruction :=
  definst "cmovpol" $ do
    pattern fun (v_3247 : reg (bv 32)) (v_3248 : reg (bv 32)) => do
      v_5138 <- getRegister pf;
      v_5141 <- getRegister v_3247;
      v_5142 <- getRegister v_3248;
      setRegister (lhs.of_reg v_3248) (mux (notBool_ (eq v_5138 (expression.bv_nat 1 1))) v_5141 v_5142);
      pure ()
    pat_end;
    pattern fun (v_3240 : Mem) (v_3243 : reg (bv 32)) => do
      v_8549 <- getRegister pf;
      v_8552 <- evaluateAddress v_3240;
      v_8553 <- load v_8552 4;
      v_8554 <- getRegister v_3243;
      setRegister (lhs.of_reg v_3243) (mux (notBool_ (eq v_8549 (expression.bv_nat 1 1))) v_8553 v_8554);
      pure ()
    pat_end

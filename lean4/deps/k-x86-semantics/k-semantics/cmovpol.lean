def cmovpol1 : instruction :=
  definst "cmovpol" $ do
    pattern fun (v_3193 : reg (bv 32)) (v_3194 : reg (bv 32)) => do
      v_5087 <- getRegister pf;
      v_5090 <- getRegister v_3193;
      v_5091 <- getRegister v_3194;
      setRegister (lhs.of_reg v_3194) (mux (notBool_ (eq v_5087 (expression.bv_nat 1 1))) v_5090 v_5091);
      pure ()
    pat_end;
    pattern fun (v_3189 : Mem) (v_3190 : reg (bv 32)) => do
      v_8536 <- getRegister pf;
      v_8539 <- evaluateAddress v_3189;
      v_8540 <- load v_8539 4;
      v_8541 <- getRegister v_3190;
      setRegister (lhs.of_reg v_3190) (mux (notBool_ (eq v_8536 (expression.bv_nat 1 1))) v_8540 v_8541);
      pure ()
    pat_end

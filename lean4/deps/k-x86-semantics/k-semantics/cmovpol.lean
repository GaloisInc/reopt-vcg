def cmovpol1 : instruction :=
  definst "cmovpol" $ do
    pattern fun (v_3181 : reg (bv 32)) (v_3182 : reg (bv 32)) => do
      v_5074 <- getRegister pf;
      v_5077 <- getRegister v_3181;
      v_5078 <- getRegister v_3182;
      setRegister (lhs.of_reg v_3182) (mux (notBool_ (eq v_5074 (expression.bv_nat 1 1))) v_5077 v_5078);
      pure ()
    pat_end;
    pattern fun (v_3177 : Mem) (v_3178 : reg (bv 32)) => do
      v_8563 <- getRegister pf;
      v_8566 <- evaluateAddress v_3177;
      v_8567 <- load v_8566 4;
      v_8568 <- getRegister v_3178;
      setRegister (lhs.of_reg v_3178) (mux (notBool_ (eq v_8563 (expression.bv_nat 1 1))) v_8567 v_8568);
      pure ()
    pat_end

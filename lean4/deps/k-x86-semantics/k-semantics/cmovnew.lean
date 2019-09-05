def cmovnew1 : instruction :=
  definst "cmovnew" $ do
    pattern fun (v_2933 : reg (bv 16)) (v_2934 : reg (bv 16)) => do
      v_4727 <- getRegister zf;
      v_4730 <- getRegister v_2933;
      v_4731 <- getRegister v_2934;
      setRegister (lhs.of_reg v_2934) (mux (notBool_ (eq v_4727 (expression.bv_nat 1 1))) v_4730 v_4731);
      pure ()
    pat_end;
    pattern fun (v_2928 : Mem) (v_2929 : reg (bv 16)) => do
      v_8246 <- getRegister zf;
      v_8249 <- evaluateAddress v_2928;
      v_8250 <- load v_8249 2;
      v_8251 <- getRegister v_2929;
      setRegister (lhs.of_reg v_2929) (mux (notBool_ (eq v_8246 (expression.bv_nat 1 1))) v_8250 v_8251);
      pure ()
    pat_end

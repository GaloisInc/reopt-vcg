def cmovncw1 : instruction :=
  definst "cmovncw" $ do
    pattern fun (v_2906 : reg (bv 16)) (v_2907 : reg (bv 16)) => do
      v_4694 <- getRegister cf;
      v_4697 <- getRegister v_2906;
      v_4698 <- getRegister v_2907;
      setRegister (lhs.of_reg v_2907) (mux (notBool_ (eq v_4694 (expression.bv_nat 1 1))) v_4697 v_4698);
      pure ()
    pat_end;
    pattern fun (v_2901 : Mem) (v_2902 : reg (bv 16)) => do
      v_8222 <- getRegister cf;
      v_8225 <- evaluateAddress v_2901;
      v_8226 <- load v_8225 2;
      v_8227 <- getRegister v_2902;
      setRegister (lhs.of_reg v_2902) (mux (notBool_ (eq v_8222 (expression.bv_nat 1 1))) v_8226 v_8227);
      pure ()
    pat_end

def cmovncq1 : instruction :=
  definst "cmovncq" $ do
    pattern fun (v_2897 : reg (bv 64)) (v_2898 : reg (bv 64)) => do
      v_4683 <- getRegister cf;
      v_4686 <- getRegister v_2897;
      v_4687 <- getRegister v_2898;
      setRegister (lhs.of_reg v_2898) (mux (notBool_ (eq v_4683 (expression.bv_nat 1 1))) v_4686 v_4687);
      pure ()
    pat_end;
    pattern fun (v_2892 : Mem) (v_2893 : reg (bv 64)) => do
      v_8214 <- getRegister cf;
      v_8217 <- evaluateAddress v_2892;
      v_8218 <- load v_8217 8;
      v_8219 <- getRegister v_2893;
      setRegister (lhs.of_reg v_2893) (mux (notBool_ (eq v_8214 (expression.bv_nat 1 1))) v_8218 v_8219);
      pure ()
    pat_end

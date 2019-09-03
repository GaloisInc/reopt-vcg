def cmovnbl1 : instruction :=
  definst "cmovnbl" $ do
    pattern fun (v_2809 : reg (bv 32)) (v_2810 : reg (bv 32)) => do
      v_4588 <- getRegister cf;
      v_4591 <- getRegister v_2809;
      v_4592 <- getRegister v_2810;
      setRegister (lhs.of_reg v_2810) (mux (notBool_ (eq v_4588 (expression.bv_nat 1 1))) v_4591 v_4592);
      pure ()
    pat_end;
    pattern fun (v_2805 : Mem) (v_2806 : reg (bv 32)) => do
      v_8169 <- getRegister cf;
      v_8172 <- evaluateAddress v_2805;
      v_8173 <- load v_8172 4;
      v_8174 <- getRegister v_2806;
      setRegister (lhs.of_reg v_2806) (mux (notBool_ (eq v_8169 (expression.bv_nat 1 1))) v_8173 v_8174);
      pure ()
    pat_end

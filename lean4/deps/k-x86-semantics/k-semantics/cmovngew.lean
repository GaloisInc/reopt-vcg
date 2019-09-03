def cmovngew1 : instruction :=
  definst "cmovngew" $ do
    pattern fun (v_2896 : reg (bv 16)) (v_2897 : reg (bv 16)) => do
      v_4702 <- getRegister sf;
      v_4704 <- getRegister of;
      v_4708 <- getRegister v_2896;
      v_4709 <- getRegister v_2897;
      setRegister (lhs.of_reg v_2897) (mux (notBool_ (eq (eq v_4702 (expression.bv_nat 1 1)) (eq v_4704 (expression.bv_nat 1 1)))) v_4708 v_4709);
      pure ()
    pat_end;
    pattern fun (v_2893 : Mem) (v_2892 : reg (bv 16)) => do
      v_8290 <- getRegister sf;
      v_8292 <- getRegister of;
      v_8296 <- evaluateAddress v_2893;
      v_8297 <- load v_8296 2;
      v_8298 <- getRegister v_2892;
      setRegister (lhs.of_reg v_2892) (mux (notBool_ (eq (eq v_8290 (expression.bv_nat 1 1)) (eq v_8292 (expression.bv_nat 1 1)))) v_8297 v_8298);
      pure ()
    pat_end

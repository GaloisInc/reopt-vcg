def cmovow1 : instruction :=
  definst "cmovow" $ do
    pattern fun (v_3150 : reg (bv 16)) (v_3151 : reg (bv 16)) => do
      v_5037 <- getRegister of;
      v_5039 <- getRegister v_3150;
      v_5040 <- getRegister v_3151;
      setRegister (lhs.of_reg v_3151) (mux (eq v_5037 (expression.bv_nat 1 1)) v_5039 v_5040);
      pure ()
    pat_end;
    pattern fun (v_3144 : Mem) (v_3146 : reg (bv 16)) => do
      v_8501 <- getRegister of;
      v_8503 <- evaluateAddress v_3144;
      v_8504 <- load v_8503 2;
      v_8505 <- getRegister v_3146;
      setRegister (lhs.of_reg v_3146) (mux (eq v_8501 (expression.bv_nat 1 1)) v_8504 v_8505);
      pure ()
    pat_end

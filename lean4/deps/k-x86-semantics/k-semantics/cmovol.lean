def cmovol1 : instruction :=
  definst "cmovol" $ do
    pattern fun (v_3184 : reg (bv 32)) (v_3185 : reg (bv 32)) => do
      v_5068 <- getRegister of;
      v_5070 <- getRegister v_3184;
      v_5071 <- getRegister v_3185;
      setRegister (lhs.of_reg v_3185) (mux (eq v_5068 (expression.bv_nat 1 1)) v_5070 v_5071);
      pure ()
    pat_end;
    pattern fun (v_3177 : Mem) (v_3180 : reg (bv 32)) => do
      v_8500 <- getRegister of;
      v_8502 <- evaluateAddress v_3177;
      v_8503 <- load v_8502 4;
      v_8504 <- getRegister v_3180;
      setRegister (lhs.of_reg v_3180) (mux (eq v_8500 (expression.bv_nat 1 1)) v_8503 v_8504);
      pure ()
    pat_end

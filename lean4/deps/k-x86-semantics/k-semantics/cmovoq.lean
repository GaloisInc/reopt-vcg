def cmovoq1 : instruction :=
  definst "cmovoq" $ do
    pattern fun (v_3139 : reg (bv 64)) (v_3140 : reg (bv 64)) => do
      v_5027 <- getRegister of;
      v_5029 <- getRegister v_3139;
      v_5030 <- getRegister v_3140;
      setRegister (lhs.of_reg v_3140) (mux (eq v_5027 (expression.bv_nat 1 1)) v_5029 v_5030);
      pure ()
    pat_end;
    pattern fun (v_3135 : Mem) (v_3136 : reg (bv 64)) => do
      v_8494 <- getRegister of;
      v_8496 <- evaluateAddress v_3135;
      v_8497 <- load v_8496 8;
      v_8498 <- getRegister v_3136;
      setRegister (lhs.of_reg v_3136) (mux (eq v_8494 (expression.bv_nat 1 1)) v_8497 v_8498);
      pure ()
    pat_end

def cmovoq1 : instruction :=
  definst "cmovoq" $ do
    pattern fun (v_3128 : reg (bv 64)) (v_3129 : reg (bv 64)) => do
      v_5014 <- getRegister of;
      v_5016 <- getRegister v_3128;
      v_5017 <- getRegister v_3129;
      setRegister (lhs.of_reg v_3129) (mux (eq v_5014 (expression.bv_nat 1 1)) v_5016 v_5017);
      pure ()
    pat_end;
    pattern fun (v_3123 : Mem) (v_3124 : reg (bv 64)) => do
      v_8521 <- getRegister of;
      v_8523 <- evaluateAddress v_3123;
      v_8524 <- load v_8523 8;
      v_8525 <- getRegister v_3124;
      setRegister (lhs.of_reg v_3124) (mux (eq v_8521 (expression.bv_nat 1 1)) v_8524 v_8525);
      pure ()
    pat_end

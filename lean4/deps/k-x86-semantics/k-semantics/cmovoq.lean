def cmovoq1 : instruction :=
  definst "cmovoq" $ do
    pattern fun (v_3191 : reg (bv 64)) (v_3192 : reg (bv 64)) => do
      v_5078 <- getRegister of;
      v_5080 <- getRegister v_3191;
      v_5081 <- getRegister v_3192;
      setRegister (lhs.of_reg v_3192) (mux (eq v_5078 (expression.bv_nat 1 1)) v_5080 v_5081);
      pure ()
    pat_end;
    pattern fun (v_3186 : Mem) (v_3187 : reg (bv 64)) => do
      v_8507 <- getRegister of;
      v_8509 <- evaluateAddress v_3186;
      v_8510 <- load v_8509 8;
      v_8511 <- getRegister v_3187;
      setRegister (lhs.of_reg v_3187) (mux (eq v_8507 (expression.bv_nat 1 1)) v_8510 v_8511);
      pure ()
    pat_end

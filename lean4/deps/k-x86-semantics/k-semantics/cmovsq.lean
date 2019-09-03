def cmovsq1 : instruction :=
  definst "cmovsq" $ do
    pattern fun (v_3252 : reg (bv 64)) (v_3253 : reg (bv 64)) => do
      v_5147 <- getRegister sf;
      v_5149 <- getRegister v_3252;
      v_5150 <- getRegister v_3253;
      setRegister (lhs.of_reg v_3253) (mux (eq v_5147 (expression.bv_nat 1 1)) v_5149 v_5150);
      pure ()
    pat_end;
    pattern fun (v_3243 : Mem) (v_3244 : reg (bv 64)) => do
      v_8610 <- getRegister sf;
      v_8612 <- evaluateAddress v_3243;
      v_8613 <- load v_8612 8;
      v_8614 <- getRegister v_3244;
      setRegister (lhs.of_reg v_3244) (mux (eq v_8610 (expression.bv_nat 1 1)) v_8613 v_8614);
      pure ()
    pat_end

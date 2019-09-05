def cmovsq1 : instruction :=
  definst "cmovsq" $ do
    pattern fun (v_3315 : reg (bv 64)) (v_3316 : reg (bv 64)) => do
      v_5211 <- getRegister sf;
      v_5213 <- getRegister v_3315;
      v_5214 <- getRegister v_3316;
      setRegister (lhs.of_reg v_3316) (mux (eq v_5211 (expression.bv_nat 1 1)) v_5213 v_5214);
      pure ()
    pat_end;
    pattern fun (v_3306 : Mem) (v_3307 : reg (bv 64)) => do
      v_8596 <- getRegister sf;
      v_8598 <- evaluateAddress v_3306;
      v_8599 <- load v_8598 8;
      v_8600 <- getRegister v_3307;
      setRegister (lhs.of_reg v_3307) (mux (eq v_8596 (expression.bv_nat 1 1)) v_8599 v_8600);
      pure ()
    pat_end

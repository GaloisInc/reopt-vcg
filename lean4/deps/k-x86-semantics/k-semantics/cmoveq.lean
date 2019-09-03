def cmoveq1 : instruction :=
  definst "cmoveq" $ do
    pattern fun (v_2554 : reg (bv 64)) (v_2555 : reg (bv 64)) => do
      v_4241 <- getRegister zf;
      v_4243 <- getRegister v_2554;
      v_4244 <- getRegister v_2555;
      setRegister (lhs.of_reg v_2555) (mux (eq v_4241 (expression.bv_nat 1 1)) v_4243 v_4244);
      pure ()
    pat_end;
    pattern fun (v_2550 : Mem) (v_2551 : reg (bv 64)) => do
      v_7915 <- getRegister zf;
      v_7917 <- evaluateAddress v_2550;
      v_7918 <- load v_7917 8;
      v_7919 <- getRegister v_2551;
      setRegister (lhs.of_reg v_2551) (mux (eq v_7915 (expression.bv_nat 1 1)) v_7918 v_7919);
      pure ()
    pat_end

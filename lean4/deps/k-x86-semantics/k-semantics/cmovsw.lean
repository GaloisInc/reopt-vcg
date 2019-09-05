def cmovsw1 : instruction :=
  definst "cmovsw" $ do
    pattern fun (v_3332 : reg (bv 16)) (v_3333 : reg (bv 16)) => do
      v_5226 <- getRegister sf;
      v_5228 <- getRegister v_3332;
      v_5229 <- getRegister v_3333;
      setRegister (lhs.of_reg v_3333) (mux (eq v_5226 (expression.bv_nat 1 1)) v_5228 v_5229);
      pure ()
    pat_end;
    pattern fun (v_3323 : Mem) (v_3324 : reg (bv 16)) => do
      v_8604 <- getRegister sf;
      v_8606 <- evaluateAddress v_3323;
      v_8607 <- load v_8606 2;
      v_8608 <- getRegister v_3324;
      setRegister (lhs.of_reg v_3324) (mux (eq v_8604 (expression.bv_nat 1 1)) v_8607 v_8608);
      pure ()
    pat_end

def cmovzq1 : instruction :=
  definst "cmovzq" $ do
    pattern fun (v_3298 : reg (bv 64)) (v_3299 : reg (bv 64)) => do
      v_5195 <- getRegister zf;
      v_5197 <- getRegister v_3298;
      v_5198 <- getRegister v_3299;
      setRegister (lhs.of_reg v_3299) (mux (eq v_5195 (expression.bv_nat 1 1)) v_5197 v_5198);
      pure ()
    pat_end;
    pattern fun (v_3294 : Mem) (v_3295 : reg (bv 64)) => do
      v_8605 <- getRegister zf;
      v_8607 <- evaluateAddress v_3294;
      v_8608 <- load v_8607 8;
      v_8609 <- getRegister v_3295;
      setRegister (lhs.of_reg v_3295) (mux (eq v_8605 (expression.bv_nat 1 1)) v_8608 v_8609);
      pure ()
    pat_end

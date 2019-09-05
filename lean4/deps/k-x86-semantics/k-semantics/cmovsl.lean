def cmovsl1 : instruction :=
  definst "cmovsl" $ do
    pattern fun (v_3300 : reg (bv 32)) (v_3301 : reg (bv 32)) => do
      v_5196 <- getRegister sf;
      v_5198 <- getRegister v_3300;
      v_5199 <- getRegister v_3301;
      setRegister (lhs.of_reg v_3301) (mux (eq v_5196 (expression.bv_nat 1 1)) v_5198 v_5199);
      pure ()
    pat_end;
    pattern fun (v_3289 : Mem) (v_3292 : reg (bv 32)) => do
      v_8588 <- getRegister sf;
      v_8590 <- evaluateAddress v_3289;
      v_8591 <- load v_8590 4;
      v_8592 <- getRegister v_3292;
      setRegister (lhs.of_reg v_3292) (mux (eq v_8588 (expression.bv_nat 1 1)) v_8591 v_8592);
      pure ()
    pat_end

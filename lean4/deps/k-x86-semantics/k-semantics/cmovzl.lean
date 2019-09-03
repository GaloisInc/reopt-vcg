def cmovzl1 : instruction :=
  definst "cmovzl" $ do
    pattern fun (v_3289 : reg (bv 32)) (v_3290 : reg (bv 32)) => do
      v_5185 <- getRegister zf;
      v_5187 <- getRegister v_3289;
      v_5188 <- getRegister v_3290;
      setRegister (lhs.of_reg v_3290) (mux (eq v_5185 (expression.bv_nat 1 1)) v_5187 v_5188);
      pure ()
    pat_end;
    pattern fun (v_3285 : Mem) (v_3286 : reg (bv 32)) => do
      v_8598 <- getRegister zf;
      v_8600 <- evaluateAddress v_3285;
      v_8601 <- load v_8600 4;
      v_8602 <- getRegister v_3286;
      setRegister (lhs.of_reg v_3286) (mux (eq v_8598 (expression.bv_nat 1 1)) v_8601 v_8602);
      pure ()
    pat_end

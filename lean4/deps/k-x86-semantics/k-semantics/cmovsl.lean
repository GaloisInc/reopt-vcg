def cmovsl1 : instruction :=
  definst "cmovsl" $ do
    pattern fun (v_3246 : reg (bv 32)) (v_3247 : reg (bv 32)) => do
      v_5145 <- getRegister sf;
      v_5147 <- getRegister v_3246;
      v_5148 <- getRegister v_3247;
      setRegister (lhs.of_reg v_3247) (mux (eq v_5145 (expression.bv_nat 1 1)) v_5147 v_5148);
      pure ()
    pat_end;
    pattern fun (v_3238 : Mem) (v_3239 : reg (bv 32)) => do
      v_8575 <- getRegister sf;
      v_8577 <- evaluateAddress v_3238;
      v_8578 <- load v_8577 4;
      v_8579 <- getRegister v_3239;
      setRegister (lhs.of_reg v_3239) (mux (eq v_8575 (expression.bv_nat 1 1)) v_8578 v_8579);
      pure ()
    pat_end

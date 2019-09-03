def cmovpl1 : instruction :=
  definst "cmovpl" $ do
    pattern fun (v_3184 : reg (bv 32)) (v_3185 : reg (bv 32)) => do
      v_5077 <- getRegister pf;
      v_5079 <- getRegister v_3184;
      v_5080 <- getRegister v_3185;
      setRegister (lhs.of_reg v_3185) (mux (eq v_5077 (expression.bv_nat 1 1)) v_5079 v_5080);
      pure ()
    pat_end;
    pattern fun (v_3180 : Mem) (v_3181 : reg (bv 32)) => do
      v_8529 <- getRegister pf;
      v_8531 <- evaluateAddress v_3180;
      v_8532 <- load v_8531 4;
      v_8533 <- getRegister v_3181;
      setRegister (lhs.of_reg v_3181) (mux (eq v_8529 (expression.bv_nat 1 1)) v_8532 v_8533);
      pure ()
    pat_end

def cmovzq1 : instruction :=
  definst "cmovzq" $ do
    pattern fun (v_3287 : reg (bv 64)) (v_3288 : reg (bv 64)) => do
      v_5182 <- getRegister zf;
      v_5184 <- getRegister v_3287;
      v_5185 <- getRegister v_3288;
      setRegister (lhs.of_reg v_3288) (mux (eq v_5182 (expression.bv_nat 1 1)) v_5184 v_5185);
      pure ()
    pat_end;
    pattern fun (v_3282 : Mem) (v_3283 : reg (bv 64)) => do
      v_8632 <- getRegister zf;
      v_8634 <- evaluateAddress v_3282;
      v_8635 <- load v_8634 8;
      v_8636 <- getRegister v_3283;
      setRegister (lhs.of_reg v_3283) (mux (eq v_8632 (expression.bv_nat 1 1)) v_8635 v_8636);
      pure ()
    pat_end

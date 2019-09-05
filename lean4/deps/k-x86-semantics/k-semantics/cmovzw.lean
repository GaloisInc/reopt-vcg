def cmovzw1 : instruction :=
  definst "cmovzw" $ do
    pattern fun (v_3359 : reg (bv 16)) (v_3360 : reg (bv 16)) => do
      v_5256 <- getRegister zf;
      v_5258 <- getRegister v_3359;
      v_5259 <- getRegister v_3360;
      setRegister (lhs.of_reg v_3360) (mux (eq v_5256 (expression.bv_nat 1 1)) v_5258 v_5259);
      pure ()
    pat_end;
    pattern fun (v_3354 : Mem) (v_3355 : reg (bv 16)) => do
      v_8625 <- getRegister zf;
      v_8627 <- evaluateAddress v_3354;
      v_8628 <- load v_8627 2;
      v_8629 <- getRegister v_3355;
      setRegister (lhs.of_reg v_3355) (mux (eq v_8625 (expression.bv_nat 1 1)) v_8628 v_8629);
      pure ()
    pat_end

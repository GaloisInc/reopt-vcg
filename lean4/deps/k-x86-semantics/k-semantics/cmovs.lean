def cmovs1 : instruction :=
  definst "cmovs" $ do
    pattern fun (v_3285 : Mem) (v_3288 : reg (bv 32)) => do
      v_9069 <- getRegister sf;
      v_9071 <- evaluateAddress v_3285;
      v_9072 <- load v_9071 4;
      v_9073 <- getRegister v_3288;
      setRegister (lhs.of_reg v_3288) (mux (eq v_9069 (expression.bv_nat 1 1)) v_9072 v_9073);
      pure ()
    pat_end;
    pattern fun (v_3303 : Mem) (v_3302 : reg (bv 64)) => do
      v_9076 <- getRegister sf;
      v_9078 <- evaluateAddress v_3303;
      v_9079 <- load v_9078 8;
      v_9080 <- getRegister v_3302;
      setRegister (lhs.of_reg v_3302) (mux (eq v_9076 (expression.bv_nat 1 1)) v_9079 v_9080);
      pure ()
    pat_end;
    pattern fun (v_3320 : Mem) (v_3319 : reg (bv 16)) => do
      v_9083 <- getRegister sf;
      v_9085 <- evaluateAddress v_3320;
      v_9086 <- load v_9085 2;
      v_9087 <- getRegister v_3319;
      setRegister (lhs.of_reg v_3319) (mux (eq v_9083 (expression.bv_nat 1 1)) v_9086 v_9087);
      pure ()
    pat_end

def cmovs1 : instruction :=
  definst "cmovs" $ do
    pattern fun (v_3234 : Mem) (v_3235 : reg (bv 32)) => do
      v_9088 <- getRegister sf;
      v_9090 <- evaluateAddress v_3234;
      v_9091 <- load v_9090 4;
      v_9092 <- getRegister v_3235;
      setRegister (lhs.of_reg v_3235) (mux (eq v_9088 (expression.bv_nat 1 1)) v_9091 v_9092);
      pure ()
    pat_end;
    pattern fun (v_3251 : Mem) (v_3252 : reg (bv 64)) => do
      v_9095 <- getRegister sf;
      v_9097 <- evaluateAddress v_3251;
      v_9098 <- load v_9097 8;
      v_9099 <- getRegister v_3252;
      setRegister (lhs.of_reg v_3252) (mux (eq v_9095 (expression.bv_nat 1 1)) v_9098 v_9099);
      pure ()
    pat_end;
    pattern fun (v_3268 : Mem) (v_3270 : reg (bv 16)) => do
      v_9102 <- getRegister sf;
      v_9104 <- evaluateAddress v_3268;
      v_9105 <- load v_9104 2;
      v_9106 <- getRegister v_3270;
      setRegister (lhs.of_reg v_3270) (mux (eq v_9102 (expression.bv_nat 1 1)) v_9105 v_9106);
      pure ()
    pat_end

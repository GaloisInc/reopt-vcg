def pushq1 : instruction :=
  definst "pushq" $ do
    pattern fun (v_3294 : imm int) => do
      v_10020 <- getRegister rsp;
      v_10021 <- eval (sub v_10020 (expression.bv_nat 64 8));
      store v_10021 (handleImmediateWithSignExtend v_3294 32 64) 8;
      setRegister rsp v_10021;
      pure ()
    pat_end;
    pattern fun (v_3297 : Mem) => do
      v_15284 <- getRegister rsp;
      v_15285 <- eval (sub v_15284 (expression.bv_nat 64 8));
      v_15286 <- evaluateAddress v_3297;
      v_15287 <- load v_15286 8;
      store v_15285 v_15287 8;
      setRegister rsp v_15285;
      pure ()
    pat_end

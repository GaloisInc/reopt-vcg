def pushq1 : instruction :=
  definst "pushq" $ do
    pattern fun (v_3245 : imm int) => do
      v_10143 <- getRegister rsp;
      v_10144 <- eval (sub v_10143 (expression.bv_nat 64 8));
      store v_10144 (handleImmediateWithSignExtend v_3245 32 64) 8;
      setRegister rsp v_10144;
      pure ()
    pat_end;
    pattern fun (v_3248 : Mem) => do
      v_15487 <- getRegister rsp;
      v_15488 <- eval (sub v_15487 (expression.bv_nat 64 8));
      v_15489 <- evaluateAddress v_3248;
      v_15490 <- load v_15489 8;
      store v_15488 (mi 64 (svalueMInt v_15490)) 8;
      setRegister rsp v_15488;
      pure ()
    pat_end

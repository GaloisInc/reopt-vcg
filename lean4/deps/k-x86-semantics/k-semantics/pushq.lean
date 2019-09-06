def pushq1 : instruction :=
  definst "pushq" $ do
    pattern fun (v_3321 : imm int) => do
      v_9996 <- getRegister rsp;
      v_9997 <- eval (sub v_9996 (expression.bv_nat 64 8));
      store v_9997 (handleImmediateWithSignExtend v_3321 32 64) 8;
      setRegister rsp v_9997;
      pure ()
    pat_end;
    pattern fun (v_3325 : Mem) => do
      v_15260 <- getRegister rsp;
      v_15261 <- eval (sub v_15260 (expression.bv_nat 64 8));
      v_15262 <- evaluateAddress v_3325;
      v_15263 <- load v_15262 8;
      store v_15261 v_15263 8;
      setRegister rsp v_15261;
      pure ()
    pat_end

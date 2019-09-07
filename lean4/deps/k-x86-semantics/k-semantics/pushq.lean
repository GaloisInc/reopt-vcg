def pushq1 : instruction :=
  definst "pushq" $ do
    pattern fun (imm_0 : imm int) => do
      v_1 <- getRegister rsp;
      v_2 <- eval (sub v_1 (expression.bv_nat 64 8));
      store v_2 (handleImmediateWithSignExtend imm_0 32 64) 8;
      setRegister rsp v_2;
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) => do
      v_1 <- getRegister rsp;
      v_2 <- eval (sub v_1 (expression.bv_nat 64 8));
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 8;
      store v_2 v_4 8;
      setRegister rsp v_2;
      pure ()
    pat_end

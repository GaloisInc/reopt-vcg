def pushq1 : instruction :=
  definst "pushq" $ do
    pattern fun (v_3230 : imm int) => do
      v_10460 <- getRegister rsp;
      v_10461 <- eval (sub v_10460 (expression.bv_nat 64 8));
      store v_10461 (handleImmediateWithSignExtend v_3230 32 64) 8;
      setRegister rsp v_10461;
      pure ()
    pat_end;
    pattern fun (v_3233 : Mem) => do
      v_16106 <- getRegister rsp;
      v_16107 <- eval (sub v_16106 (expression.bv_nat 64 8));
      v_16108 <- evaluateAddress v_3233;
      v_16109 <- load v_16108 8;
      store v_16107 (mi 64 (svalueMInt v_16109)) 8;
      setRegister rsp v_16107;
      pure ()
    pat_end

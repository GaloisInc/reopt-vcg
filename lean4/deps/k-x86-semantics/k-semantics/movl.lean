def movl1 : instruction :=
  definst "movl" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      store v_2 (handleImmediateWithSignExtend imm_0 32 32) 4;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) => do
      setRegister (lhs.of_reg r32_1) (handleImmediateWithSignExtend imm_0 32 32);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 4;
      setRegister (lhs.of_reg r32_1) v_3;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r32_0;
      store v_2 v_3 4;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister r32_0;
      setRegister (lhs.of_reg r32_1) v_2;
      pure ()
    pat_end

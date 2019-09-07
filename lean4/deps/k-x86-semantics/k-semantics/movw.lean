def movw1 : instruction :=
  definst "movw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      store v_2 (handleImmediateWithSignExtend imm_0 16 16) 2;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      setRegister (lhs.of_reg r16_1) (handleImmediateWithSignExtend imm_0 16 16);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 2;
      setRegister (lhs.of_reg r16_1) v_3;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r16_0;
      store v_2 v_3 2;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister r16_0;
      setRegister (lhs.of_reg r16_1) v_2;
      pure ()
    pat_end

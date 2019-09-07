def movq1 : instruction :=
  definst "movq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      store v_2 (sext (handleImmediateWithSignExtend imm_0 32 32) 64) 8;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      setRegister (lhs.of_reg r64_1) (handleImmediateWithSignExtend imm_0 64 64);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r64_1 : reg (bv 64)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg r64_1) v_3;
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- evaluateAddress mem_0;
      v_3 <- load v_2 8;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) v_3);
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r64_0;
      store v_2 v_3 8;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_0;
      setRegister (lhs.of_reg r64_1) v_2;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister r64_0;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) v_2);
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister xmm_0;
      store v_2 (extract v_3 64 128) 8;
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg r64_1) (extract v_2 64 128);
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (expression.bv_nat 64 0) (extract v_2 64 128));
      pure ()
    pat_end

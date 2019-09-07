def btl1 : instruction :=
  definst "btl" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- load (add v_2 (concat (expression.bv_nat 59 0) (bv_and (extract v_3 0 5) (expression.bv_nat 5 3)))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_4 (concat (expression.bv_nat 5 0) (bv_and (extract v_3 5 8) (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister r32_1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 (sext (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 31)) 32)) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r32_0;
      v_4 <- load (add v_2 (concat (expression.bv_nat 3 0) (extract (sext v_3 64) 0 61))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_4 (concat (expression.bv_nat 5 0) (extract v_3 29 32))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister r32_1;
      v_3 <- getRegister r32_0;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 (bv_and v_3 (expression.bv_nat 32 31))) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end

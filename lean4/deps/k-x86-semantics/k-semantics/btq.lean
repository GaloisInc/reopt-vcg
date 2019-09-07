def btq1 : instruction :=
  definst "btq" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- load (add v_2 (concat (expression.bv_nat 59 0) (bv_and (extract v_3 0 5) (expression.bv_nat 5 7)))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_4 (concat (expression.bv_nat 5 0) (bv_and (extract v_3 5 8) (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 (sext (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 63)) 64)) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r64_0;
      v_4 <- load (add v_2 (concat (expression.bv_nat 3 0) (extract v_3 0 61))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_4 (concat (expression.bv_nat 5 0) (extract v_3 61 64))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r64_0 : reg (bv 64)) (r64_1 : reg (bv 64)) => do
      v_2 <- getRegister r64_1;
      v_3 <- getRegister r64_0;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 (bv_and v_3 (expression.bv_nat 64 63))) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end

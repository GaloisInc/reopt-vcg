def btrw1 : instruction :=
  definst "btrw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      v_4 <- eval (add v_2 (concat (expression.bv_nat 59 0) (bv_and (extract v_3 0 5) (expression.bv_nat 5 1))));
      v_5 <- load v_4 1;
      v_6 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_3 5 8) (expression.bv_nat 3 7)));
      store v_4 (bv_and v_5 (bv_xor (extract (shl (expression.bv_nat 8 1) v_6) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5 v_6) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister r16_1;
      v_3 <- eval (sext (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 15)) 16);
      setRegister (lhs.of_reg r16_1) (bv_and v_2 (bv_xor (extract (shl (expression.bv_nat 16 1) v_3) 0 16) (expression.bv_nat 16 65535)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 v_3) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister r16_0;
      v_4 <- eval (add v_2 (concat (expression.bv_nat 3 0) (extract (sext v_3 64) 0 61)));
      v_5 <- load v_4 1;
      v_6 <- eval (concat (expression.bv_nat 5 0) (extract v_3 13 16));
      store v_4 (bv_and v_5 (bv_xor (extract (shl (expression.bv_nat 8 1) v_6) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5 v_6) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister r16_1;
      v_3 <- getRegister r16_0;
      v_4 <- eval (bv_and v_3 (expression.bv_nat 16 15));
      setRegister (lhs.of_reg r16_1) (bv_and v_2 (bv_xor (extract (shl (expression.bv_nat 16 1) v_4) 0 16) (expression.bv_nat 16 65535)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 v_4) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end

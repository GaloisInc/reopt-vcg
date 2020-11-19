def btsw : instruction :=
  definst "btsw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_4 : expression (bv 5)) <- eval (extract v_3 0 5);
      v_5 <- eval (add v_2 (concat (expression.bv_nat 59 0) (bv_and v_4 (expression.bv_nat 5 1))));
      v_6 <- load v_5 1;
      (v_7 : expression (bv 3)) <- eval (extract v_3 5 8);
      v_8 <- eval (concat (expression.bv_nat 5 0) (bv_and v_7 (expression.bv_nat 3 7)));
      (v_9 : expression (bv 8)) <- eval (extract (shl (expression.bv_nat 8 1) v_8) 0 8);
      store v_5 (bv_or v_6 v_9) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6 v_8) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_1);
      v_3 <- eval (sext (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 15)) 16);
      (v_4 : expression (bv 16)) <- eval (extract (shl (expression.bv_nat 16 1) v_3) 0 16);
      setRegister (lhs.of_reg r16_1) (bv_or v_2 v_4);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 v_3) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg r16_0);
      (v_4 : expression (bv 61)) <- eval (extract (sext v_3 64) 0 61);
      v_5 <- eval (add v_2 (concat (expression.bv_nat 3 0) v_4));
      v_6 <- load v_5 1;
      (v_7 : expression (bv 3)) <- eval (extract v_3 13 16);
      v_8 <- eval (concat (expression.bv_nat 5 0) v_7);
      (v_9 : expression (bv 8)) <- eval (extract (shl (expression.bv_nat 8 1) v_8) 0 8);
      store v_5 (bv_or v_6 v_9) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6 v_8) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_1);
      v_3 <- getRegister (lhs.of_reg r16_0);
      v_4 <- eval (bv_and v_3 (expression.bv_nat 16 15));
      (v_5 : expression (bv 16)) <- eval (extract (shl (expression.bv_nat 16 1) v_4) 0 16);
      setRegister (lhs.of_reg r16_1) (bv_or v_2 v_5);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 v_4) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end

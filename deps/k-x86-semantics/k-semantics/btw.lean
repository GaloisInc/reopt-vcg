def btw : instruction :=
  definst "btw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- eval (handleImmediateWithSignExtend imm_0 8 8);
      (v_4 : expression (bv 5)) <- eval (extract v_3 0 5);
      v_5 <- load (add v_2 (concat (expression.bv_nat 59 0) (bv_and v_4 (expression.bv_nat 5 1)))) 1;
      (v_6 : expression (bv 3)) <- eval (extract v_3 5 8);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5 (concat (expression.bv_nat 5 0) (bv_and v_6 (expression.bv_nat 3 7)))) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_1);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 (sext (bv_and (handleImmediateWithSignExtend imm_0 8 8) (expression.bv_nat 8 15)) 16)) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- getRegister (lhs.of_reg r16_0);
      (v_4 : expression (bv 61)) <- eval (extract (sext v_3 64) 0 61);
      v_5 <- load (add v_2 (concat (expression.bv_nat 3 0) v_4)) 1;
      (v_6 : expression (bv 3)) <- eval (extract v_3 13 16);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5 (concat (expression.bv_nat 5 0) v_6)) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_1);
      v_3 <- getRegister (lhs.of_reg r16_0);
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_2 (bv_and v_3 (expression.bv_nat 16 15))) 15);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end

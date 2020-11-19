def orw : instruction :=
  definst "orw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 2;
      v_4 <- eval (bv_or v_3 (handleImmediateWithSignExtend imm_0 16 16));
      store v_2 v_4 2;
      (v_6 : expression (bv 8)) <- eval (extract v_4 8 16);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_1);
      v_3 <- eval (bv_or v_2 (handleImmediateWithSignExtend imm_0 16 16));
      (v_4 : expression (bv 8)) <- eval (extract v_3 8 16);
      setRegister (lhs.of_reg r16_1) v_3;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_4);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 2;
      v_5 <- eval (bv_or v_2 v_4);
      (v_6 : expression (bv 8)) <- eval (extract v_5 8 16);
      setRegister (lhs.of_reg r16_1) v_5;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 2;
      v_4 <- getRegister (lhs.of_reg r16_0);
      v_5 <- eval (bv_or v_3 v_4);
      store v_2 v_5 2;
      (v_7 : expression (bv 8)) <- eval (extract v_5 8 16);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_7);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_1);
      v_3 <- getRegister (lhs.of_reg r16_0);
      v_4 <- eval (bv_or v_2 v_3);
      (v_5 : expression (bv 8)) <- eval (extract v_4 8 16);
      setRegister (lhs.of_reg r16_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end

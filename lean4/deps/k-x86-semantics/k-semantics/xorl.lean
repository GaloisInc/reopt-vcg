def xorl : instruction :=
  definst "xorl" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 4;
      v_4 <- eval (bv_xor v_3 (handleImmediateWithSignExtend imm_0 32 32));
      store v_2 v_4 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4 24 32));
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg r32_1);
      v_3 <- eval (bv_xor v_2 (handleImmediateWithSignExtend imm_0 32 32));
      setRegister (lhs.of_reg r32_1) v_3;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_3 24 32));
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg r32_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 4;
      v_5 <- eval (bv_xor v_2 v_4);
      setRegister (lhs.of_reg r32_1) v_5;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5 24 32));
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 4;
      v_4 <- getRegister (lhs.of_reg r32_0);
      v_5 <- eval (bv_xor v_3 v_4);
      store v_2 v_5 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5 24 32));
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (r32_0 : reg (bv 32)) (r32_1 : reg (bv 32)) => do
      v_2 <- getRegister (lhs.of_reg r32_1);
      v_3 <- getRegister (lhs.of_reg r32_0);
      v_4 <- eval (bv_xor v_2 v_3);
      setRegister (lhs.of_reg r32_1) v_4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4 24 32));
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end

def testb : instruction :=
  definst "testb" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 1;
      v_4 <- eval (bv_and v_3 (handleImmediateWithSignExtend imm_0 8 8));
      (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (rh_1 : reg (bv 8)) => do
      v_2 <- getRegister (lhs.of_reg rh_1);
      v_3 <- eval (bv_and v_2 (handleImmediateWithSignExtend imm_0 8 8));
      (v_4 : expression (bv 8)) <- eval (extract v_3 0 8);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_4);
      setRegister sf (isBitSet v_3 0);
      setRegister zf (zeroFlag v_3);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (mem_1 : Mem) => do
      v_2 <- evaluateAddress mem_1;
      v_3 <- load v_2 1;
      v_4 <- getRegister (lhs.of_reg rh_0);
      v_5 <- eval (bv_and v_3 v_4);
      (v_6 : expression (bv 8)) <- eval (extract v_5 0 8);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_6);
      setRegister sf (isBitSet v_5 0);
      setRegister zf (zeroFlag v_5);
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) (rh_1 : reg (bv 8)) => do
      v_2 <- getRegister (lhs.of_reg rh_1);
      v_3 <- getRegister (lhs.of_reg rh_0);
      v_4 <- eval (bv_and v_2 v_3);
      (v_5 : expression (bv 8)) <- eval (extract v_4 0 8);
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag v_5);
      setRegister sf (isBitSet v_4 0);
      setRegister zf (zeroFlag v_4);
      pure ()
    pat_end
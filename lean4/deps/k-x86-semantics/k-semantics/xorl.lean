def xorl1 : instruction :=
  definst "xorl" $ do
    pattern fun (v_3425 : imm int) (v_3426 : reg (bv 32)) => do
      v_8018 <- getRegister v_3426;
      v_8020 <- eval (bv_xor v_8018 (handleImmediateWithSignExtend v_3425 32 32));
      setRegister (lhs.of_reg v_3426) v_8020;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8020 24 32));
      setRegister sf (isBitSet v_8020 0);
      setRegister zf (zeroFlag v_8020);
      pure ()
    pat_end;
    pattern fun (v_3434 : reg (bv 32)) (v_3435 : reg (bv 32)) => do
      v_8036 <- getRegister v_3435;
      v_8037 <- getRegister v_3434;
      v_8038 <- eval (bv_xor v_8036 v_8037);
      setRegister (lhs.of_reg v_3435) v_8038;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8038 24 32));
      setRegister sf (isBitSet v_8038 0);
      setRegister zf (zeroFlag v_8038);
      pure ()
    pat_end;
    pattern fun (v_3430 : Mem) (v_3431 : reg (bv 32)) => do
      v_13574 <- getRegister v_3431;
      v_13575 <- evaluateAddress v_3430;
      v_13576 <- load v_13575 4;
      v_13577 <- eval (bv_xor v_13574 v_13576);
      setRegister (lhs.of_reg v_3431) v_13577;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13577 24 32));
      setRegister sf (isBitSet v_13577 0);
      setRegister zf (zeroFlag v_13577);
      pure ()
    pat_end;
    pattern fun (v_3417 : imm int) (v_3418 : Mem) => do
      v_13678 <- evaluateAddress v_3418;
      v_13679 <- load v_13678 4;
      v_13681 <- eval (bv_xor v_13679 (handleImmediateWithSignExtend v_3417 32 32));
      store v_13678 v_13681 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13681 24 32));
      setRegister sf (isBitSet v_13681 0);
      setRegister zf (zeroFlag v_13681);
      pure ()
    pat_end;
    pattern fun (v_3422 : reg (bv 32)) (v_3421 : Mem) => do
      v_13693 <- evaluateAddress v_3421;
      v_13694 <- load v_13693 4;
      v_13695 <- getRegister v_3422;
      v_13696 <- eval (bv_xor v_13694 v_13695);
      store v_13693 v_13696 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_13696 24 32));
      setRegister sf (isBitSet v_13696 0);
      setRegister zf (zeroFlag v_13696);
      pure ()
    pat_end

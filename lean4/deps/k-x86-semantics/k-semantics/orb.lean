def orb1 : instruction :=
  definst "orb" $ do
    pattern fun (v_2991 : imm int) (v_2992 : reg (bv 8)) => do
      v_4665 <- getRegister v_2992;
      v_4667 <- eval (bv_or v_4665 (handleImmediateWithSignExtend v_2991 8 8));
      setRegister (lhs.of_reg v_2992) v_4667;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4667 0 8));
      setRegister sf (isBitSet v_4667 0);
      setRegister zf (zeroFlag v_4667);
      pure ()
    pat_end;
    pattern fun (v_3005 : reg (bv 8)) (v_3006 : reg (bv 8)) => do
      v_4697 <- getRegister v_3006;
      v_4698 <- getRegister v_3005;
      v_4699 <- eval (bv_or v_4697 v_4698);
      setRegister (lhs.of_reg v_3006) v_4699;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4699 0 8));
      setRegister sf (isBitSet v_4699 0);
      setRegister zf (zeroFlag v_4699);
      pure ()
    pat_end;
    pattern fun (v_2996 : Mem) (v_2997 : reg (bv 8)) => do
      v_8955 <- getRegister v_2997;
      v_8956 <- evaluateAddress v_2996;
      v_8957 <- load v_8956 1;
      v_8958 <- eval (bv_or v_8955 v_8957);
      setRegister (lhs.of_reg v_2997) v_8958;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8958 0 8));
      setRegister sf (isBitSet v_8958 0);
      setRegister zf (zeroFlag v_8958);
      pure ()
    pat_end;
    pattern fun (v_2960 : imm int) (v_2961 : Mem) => do
      v_10801 <- evaluateAddress v_2961;
      v_10802 <- load v_10801 1;
      v_10804 <- eval (bv_or v_10802 (handleImmediateWithSignExtend v_2960 8 8));
      store v_10801 v_10804 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10804 0 8));
      setRegister sf (isBitSet v_10804 0);
      setRegister zf (zeroFlag v_10804);
      pure ()
    pat_end;
    pattern fun (v_2969 : reg (bv 8)) (v_2968 : Mem) => do
      v_10831 <- evaluateAddress v_2968;
      v_10832 <- load v_10831 1;
      v_10833 <- getRegister v_2969;
      v_10834 <- eval (bv_or v_10832 v_10833);
      store v_10831 v_10834 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10834 0 8));
      setRegister sf (isBitSet v_10834 0);
      setRegister zf (zeroFlag v_10834);
      pure ()
    pat_end

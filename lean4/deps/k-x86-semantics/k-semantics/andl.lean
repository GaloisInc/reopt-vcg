def andl1 : instruction :=
  definst "andl" $ do
    pattern fun (v_2828 : imm int) (v_2829 : reg (bv 32)) => do
      v_5318 <- getRegister v_2829;
      v_5320 <- eval (bv_and v_5318 (handleImmediateWithSignExtend v_2828 32 32));
      setRegister (lhs.of_reg v_2829) v_5320;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5320 24 32));
      setRegister sf (isBitSet v_5320 0);
      setRegister zf (zeroFlag v_5320);
      pure ()
    pat_end;
    pattern fun (v_2837 : reg (bv 32)) (v_2838 : reg (bv 32)) => do
      v_5336 <- getRegister v_2838;
      v_5337 <- getRegister v_2837;
      v_5338 <- eval (bv_and v_5336 v_5337);
      setRegister (lhs.of_reg v_2838) v_5338;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5338 24 32));
      setRegister sf (isBitSet v_5338 0);
      setRegister zf (zeroFlag v_5338);
      pure ()
    pat_end;
    pattern fun (v_2834 : Mem) (v_2833 : reg (bv 32)) => do
      v_9133 <- getRegister v_2833;
      v_9134 <- evaluateAddress v_2834;
      v_9135 <- load v_9134 4;
      v_9136 <- eval (bv_and v_9133 v_9135);
      setRegister (lhs.of_reg v_2833) v_9136;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9136 24 32));
      setRegister sf (isBitSet v_9136 0);
      setRegister zf (zeroFlag v_9136);
      pure ()
    pat_end;
    pattern fun (v_2820 : imm int) (v_2821 : Mem) => do
      v_10605 <- evaluateAddress v_2821;
      v_10606 <- load v_10605 4;
      v_10608 <- eval (bv_and v_10606 (handleImmediateWithSignExtend v_2820 32 32));
      store v_10605 v_10608 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10608 24 32));
      setRegister sf (isBitSet v_10608 0);
      setRegister zf (zeroFlag v_10608);
      pure ()
    pat_end;
    pattern fun (v_2824 : reg (bv 32)) (v_2825 : Mem) => do
      v_10620 <- evaluateAddress v_2825;
      v_10621 <- load v_10620 4;
      v_10622 <- getRegister v_2824;
      v_10623 <- eval (bv_and v_10621 v_10622);
      store v_10620 v_10623 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10623 24 32));
      setRegister sf (isBitSet v_10623 0);
      setRegister zf (zeroFlag v_10623);
      pure ()
    pat_end

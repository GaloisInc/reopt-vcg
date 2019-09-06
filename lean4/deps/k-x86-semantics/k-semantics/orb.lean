def orb1 : instruction :=
  definst "orb" $ do
    pattern fun (v_3017 : imm int) (v_3018 : reg (bv 8)) => do
      v_4692 <- getRegister v_3018;
      v_4694 <- eval (bv_or v_4692 (handleImmediateWithSignExtend v_3017 8 8));
      setRegister (lhs.of_reg v_3018) v_4694;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4694 0 8));
      setRegister sf (isBitSet v_4694 0);
      setRegister zf (zeroFlag v_4694);
      pure ()
    pat_end;
    pattern fun (v_3031 : reg (bv 8)) (v_3032 : reg (bv 8)) => do
      v_4724 <- getRegister v_3032;
      v_4725 <- getRegister v_3031;
      v_4726 <- eval (bv_or v_4724 v_4725);
      setRegister (lhs.of_reg v_3032) v_4726;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4726 0 8));
      setRegister sf (isBitSet v_4726 0);
      setRegister zf (zeroFlag v_4726);
      pure ()
    pat_end;
    pattern fun (v_3022 : Mem) (v_3023 : reg (bv 8)) => do
      v_8982 <- getRegister v_3023;
      v_8983 <- evaluateAddress v_3022;
      v_8984 <- load v_8983 1;
      v_8985 <- eval (bv_or v_8982 v_8984);
      setRegister (lhs.of_reg v_3023) v_8985;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8985 0 8));
      setRegister sf (isBitSet v_8985 0);
      setRegister zf (zeroFlag v_8985);
      pure ()
    pat_end;
    pattern fun (v_2987 : imm int) (v_2986 : Mem) => do
      v_10828 <- evaluateAddress v_2986;
      v_10829 <- load v_10828 1;
      v_10831 <- eval (bv_or v_10829 (handleImmediateWithSignExtend v_2987 8 8));
      store v_10828 v_10831 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10831 0 8));
      setRegister sf (isBitSet v_10831 0);
      setRegister zf (zeroFlag v_10831);
      pure ()
    pat_end;
    pattern fun (v_2995 : reg (bv 8)) (v_2994 : Mem) => do
      v_10858 <- evaluateAddress v_2994;
      v_10859 <- load v_10858 1;
      v_10860 <- getRegister v_2995;
      v_10861 <- eval (bv_or v_10859 v_10860);
      store v_10858 v_10861 1;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10861 0 8));
      setRegister sf (isBitSet v_10861 0);
      setRegister zf (zeroFlag v_10861);
      pure ()
    pat_end

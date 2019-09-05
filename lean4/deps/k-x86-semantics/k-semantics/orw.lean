def orw1 : instruction :=
  definst "orw" $ do
    pattern fun (v_3092 : imm int) (v_3094 : reg (bv 16)) => do
      v_5039 <- getRegister v_3094;
      v_5041 <- eval (bv_or v_5039 (handleImmediateWithSignExtend v_3092 16 16));
      setRegister (lhs.of_reg v_3094) v_5041;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5041 8 16));
      setRegister sf (isBitSet v_5041 0);
      setRegister zf (zeroFlag v_5041);
      pure ()
    pat_end;
    pattern fun (v_3102 : reg (bv 16)) (v_3103 : reg (bv 16)) => do
      v_5057 <- getRegister v_3103;
      v_5058 <- getRegister v_3102;
      v_5059 <- eval (bv_or v_5057 v_5058);
      setRegister (lhs.of_reg v_3103) v_5059;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5059 8 16));
      setRegister sf (isBitSet v_5059 0);
      setRegister zf (zeroFlag v_5059);
      pure ()
    pat_end;
    pattern fun (v_3097 : Mem) (v_3098 : reg (bv 16)) => do
      v_9016 <- getRegister v_3098;
      v_9017 <- evaluateAddress v_3097;
      v_9018 <- load v_9017 2;
      v_9019 <- eval (bv_or v_9016 v_9018);
      setRegister (lhs.of_reg v_3098) v_9019;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9019 8 16));
      setRegister sf (isBitSet v_9019 0);
      setRegister zf (zeroFlag v_9019);
      pure ()
    pat_end;
    pattern fun (v_3085 : imm int) (v_3084 : Mem) => do
      v_10950 <- evaluateAddress v_3084;
      v_10951 <- load v_10950 2;
      v_10953 <- eval (bv_or v_10951 (handleImmediateWithSignExtend v_3085 16 16));
      store v_10950 v_10953 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10953 8 16));
      setRegister sf (isBitSet v_10953 0);
      setRegister zf (zeroFlag v_10953);
      pure ()
    pat_end;
    pattern fun (v_3089 : reg (bv 16)) (v_3088 : Mem) => do
      v_10965 <- evaluateAddress v_3088;
      v_10966 <- load v_10965 2;
      v_10967 <- getRegister v_3089;
      v_10968 <- eval (bv_or v_10966 v_10967);
      store v_10965 v_10968 2;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10968 8 16));
      setRegister sf (isBitSet v_10968 0);
      setRegister zf (zeroFlag v_10968);
      pure ()
    pat_end

def andl1 : instruction :=
  definst "andl" $ do
    pattern fun (v_2855 : imm int) (v_2857 : reg (bv 32)) => do
      v_5199 <- getRegister v_2857;
      v_5201 <- eval (bv_and v_5199 (handleImmediateWithSignExtend v_2855 32 32));
      setRegister (lhs.of_reg v_2857) v_5201;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5201 24 32));
      setRegister sf (isBitSet v_5201 0);
      setRegister zf (zeroFlag v_5201);
      pure ()
    pat_end;
    pattern fun (v_2865 : reg (bv 32)) (v_2866 : reg (bv 32)) => do
      v_5217 <- getRegister v_2866;
      v_5218 <- getRegister v_2865;
      v_5219 <- eval (bv_and v_5217 v_5218);
      setRegister (lhs.of_reg v_2866) v_5219;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_5219 24 32));
      setRegister sf (isBitSet v_5219 0);
      setRegister zf (zeroFlag v_5219);
      pure ()
    pat_end;
    pattern fun (v_2860 : Mem) (v_2861 : reg (bv 32)) => do
      v_8957 <- getRegister v_2861;
      v_8958 <- evaluateAddress v_2860;
      v_8959 <- load v_8958 4;
      v_8960 <- eval (bv_and v_8957 v_8959);
      setRegister (lhs.of_reg v_2861) v_8960;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_8960 24 32));
      setRegister sf (isBitSet v_8960 0);
      setRegister zf (zeroFlag v_8960);
      pure ()
    pat_end;
    pattern fun (v_2848 : imm int) (v_2847 : Mem) => do
      v_10329 <- evaluateAddress v_2847;
      v_10330 <- load v_10329 4;
      v_10332 <- eval (bv_and v_10330 (handleImmediateWithSignExtend v_2848 32 32));
      store v_10329 v_10332 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10332 24 32));
      setRegister sf (isBitSet v_10332 0);
      setRegister zf (zeroFlag v_10332);
      pure ()
    pat_end;
    pattern fun (v_2852 : reg (bv 32)) (v_2851 : Mem) => do
      v_10344 <- evaluateAddress v_2851;
      v_10345 <- load v_10344 4;
      v_10346 <- getRegister v_2852;
      v_10347 <- eval (bv_and v_10345 v_10346);
      store v_10344 v_10347 4;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10347 24 32));
      setRegister sf (isBitSet v_10347 0);
      setRegister zf (zeroFlag v_10347);
      pure ()
    pat_end

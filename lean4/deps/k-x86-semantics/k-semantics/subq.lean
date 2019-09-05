def subq1 : instruction :=
  definst "subq" $ do
    pattern fun (v_3264 : imm int) (v_3266 : reg (bv 64)) => do
      v_6502 <- eval (handleImmediateWithSignExtend v_3264 32 32);
      v_6503 <- eval (sext v_6502 64);
      v_6507 <- getRegister v_3266;
      v_6509 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6503 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_6507));
      v_6510 <- eval (extract v_6509 1 65);
      v_6512 <- eval (isBitSet v_6509 1);
      v_6517 <- eval (eq (bv_xor (extract v_6503 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3266) v_6510;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_6502 27) (isBitSet v_6507 59))) (isBitSet v_6509 60)));
      setRegister cf (notBool_ (isBitSet v_6509 0));
      setRegister of (bit_and (eq v_6517 (isBitSet v_6507 0)) (notBool_ (eq v_6517 v_6512)));
      setRegister pf (parityFlag (extract v_6509 57 65));
      setRegister sf v_6512;
      setRegister zf (zeroFlag v_6510);
      pure ()
    pat_end;
    pattern fun (v_3274 : reg (bv 64)) (v_3275 : reg (bv 64)) => do
      v_6543 <- getRegister v_3274;
      v_6547 <- getRegister v_3275;
      v_6549 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_6543 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_6547));
      v_6550 <- eval (extract v_6549 1 65);
      v_6552 <- eval (isBitSet v_6549 1);
      v_6557 <- eval (eq (bv_xor (extract v_6543 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3275) v_6550;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_6543 v_6547) 59) (isBitSet v_6549 60)));
      setRegister cf (notBool_ (isBitSet v_6549 0));
      setRegister of (bit_and (eq v_6557 (isBitSet v_6547 0)) (notBool_ (eq v_6557 v_6552)));
      setRegister pf (parityFlag (extract v_6549 57 65));
      setRegister sf v_6552;
      setRegister zf (zeroFlag v_6550);
      pure ()
    pat_end;
    pattern fun (v_3269 : Mem) (v_3270 : reg (bv 64)) => do
      v_9338 <- evaluateAddress v_3269;
      v_9339 <- load v_9338 8;
      v_9343 <- getRegister v_3270;
      v_9345 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9339 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_9343));
      v_9346 <- eval (extract v_9345 1 65);
      v_9348 <- eval (isBitSet v_9345 1);
      v_9353 <- eval (eq (bv_xor (extract v_9339 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3270) v_9346;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9339 v_9343) 59) (isBitSet v_9345 60)));
      setRegister cf (notBool_ (isBitSet v_9345 0));
      setRegister of (bit_and (eq v_9353 (isBitSet v_9343 0)) (notBool_ (eq v_9353 v_9348)));
      setRegister pf (parityFlag (extract v_9345 57 65));
      setRegister sf v_9348;
      setRegister zf (zeroFlag v_9346);
      pure ()
    pat_end;
    pattern fun (v_3257 : imm int) (v_3256 : Mem) => do
      v_10950 <- evaluateAddress v_3256;
      v_10951 <- eval (handleImmediateWithSignExtend v_3257 32 32);
      v_10952 <- eval (sext v_10951 64);
      v_10956 <- load v_10950 8;
      v_10958 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10952 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_10956));
      v_10959 <- eval (extract v_10958 1 65);
      store v_10950 v_10959 8;
      v_10962 <- eval (isBitSet v_10958 1);
      v_10967 <- eval (eq (bv_xor (extract v_10952 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_10951 27) (isBitSet v_10956 59))) (isBitSet v_10958 60)));
      setRegister cf (notBool_ (isBitSet v_10958 0));
      setRegister of (bit_and (eq v_10967 (isBitSet v_10956 0)) (notBool_ (eq v_10967 v_10962)));
      setRegister pf (parityFlag (extract v_10958 57 65));
      setRegister sf v_10962;
      setRegister zf (zeroFlag v_10959);
      pure ()
    pat_end;
    pattern fun (v_3261 : reg (bv 64)) (v_3260 : Mem) => do
      v_10988 <- evaluateAddress v_3260;
      v_10989 <- getRegister v_3261;
      v_10993 <- load v_10988 8;
      v_10995 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10989 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_10993));
      v_10996 <- eval (extract v_10995 1 65);
      store v_10988 v_10996 8;
      v_10999 <- eval (isBitSet v_10995 1);
      v_11004 <- eval (eq (bv_xor (extract v_10989 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10989 v_10993) 59) (isBitSet v_10995 60)));
      setRegister cf (notBool_ (isBitSet v_10995 0));
      setRegister of (bit_and (eq v_11004 (isBitSet v_10993 0)) (notBool_ (eq v_11004 v_10999)));
      setRegister pf (parityFlag (extract v_10995 57 65));
      setRegister sf v_10999;
      setRegister zf (zeroFlag v_10996);
      pure ()
    pat_end

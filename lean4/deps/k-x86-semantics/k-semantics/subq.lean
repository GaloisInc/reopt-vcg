def subq1 : instruction :=
  definst "subq" $ do
    pattern fun (v_3292 : imm int) (v_3293 : reg (bv 64)) => do
      v_5947 <- eval (handleImmediateWithSignExtend v_3292 32 32);
      v_5948 <- eval (sext v_5947 64);
      v_5952 <- getRegister v_3293;
      v_5954 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5948 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_5952));
      v_5955 <- eval (extract v_5954 1 65);
      v_5957 <- eval (isBitSet v_5954 1);
      v_5962 <- eval (eq (bv_xor (extract v_5948 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3293) v_5955;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_5947 27) (isBitSet v_5952 59))) (isBitSet v_5954 60)));
      setRegister cf (isBitClear v_5954 0);
      setRegister of (bit_and (eq v_5962 (isBitSet v_5952 0)) (notBool_ (eq v_5962 v_5957)));
      setRegister pf (parityFlag (extract v_5954 57 65));
      setRegister sf v_5957;
      setRegister zf (zeroFlag v_5955);
      pure ()
    pat_end;
    pattern fun (v_3301 : reg (bv 64)) (v_3302 : reg (bv 64)) => do
      v_5987 <- getRegister v_3301;
      v_5991 <- getRegister v_3302;
      v_5993 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5987 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_5991));
      v_5994 <- eval (extract v_5993 1 65);
      v_5996 <- eval (isBitSet v_5993 1);
      v_6001 <- eval (eq (bv_xor (extract v_5987 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3302) v_5994;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5987 v_5991) 59) (isBitSet v_5993 60)));
      setRegister cf (isBitClear v_5993 0);
      setRegister of (bit_and (eq v_6001 (isBitSet v_5991 0)) (notBool_ (eq v_6001 v_5996)));
      setRegister pf (parityFlag (extract v_5993 57 65));
      setRegister sf v_5996;
      setRegister zf (zeroFlag v_5994);
      pure ()
    pat_end;
    pattern fun (v_3297 : Mem) (v_3298 : reg (bv 64)) => do
      v_8728 <- evaluateAddress v_3297;
      v_8729 <- load v_8728 8;
      v_8733 <- getRegister v_3298;
      v_8735 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8729 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_8733));
      v_8736 <- eval (extract v_8735 1 65);
      v_8738 <- eval (isBitSet v_8735 1);
      v_8743 <- eval (eq (bv_xor (extract v_8729 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3298) v_8736;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8729 v_8733) 59) (isBitSet v_8735 60)));
      setRegister cf (isBitClear v_8735 0);
      setRegister of (bit_and (eq v_8743 (isBitSet v_8733 0)) (notBool_ (eq v_8743 v_8738)));
      setRegister pf (parityFlag (extract v_8735 57 65));
      setRegister sf v_8738;
      setRegister zf (zeroFlag v_8736);
      pure ()
    pat_end;
    pattern fun (v_3285 : imm int) (v_3284 : Mem) => do
      v_9949 <- evaluateAddress v_3284;
      v_9950 <- eval (handleImmediateWithSignExtend v_3285 32 32);
      v_9951 <- eval (sext v_9950 64);
      v_9955 <- load v_9949 8;
      v_9957 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9951 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_9955));
      v_9958 <- eval (extract v_9957 1 65);
      store v_9949 v_9958 8;
      v_9961 <- eval (isBitSet v_9957 1);
      v_9966 <- eval (eq (bv_xor (extract v_9951 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_9950 27) (isBitSet v_9955 59))) (isBitSet v_9957 60)));
      setRegister cf (isBitClear v_9957 0);
      setRegister of (bit_and (eq v_9966 (isBitSet v_9955 0)) (notBool_ (eq v_9966 v_9961)));
      setRegister pf (parityFlag (extract v_9957 57 65));
      setRegister sf v_9961;
      setRegister zf (zeroFlag v_9958);
      pure ()
    pat_end;
    pattern fun (v_3289 : reg (bv 64)) (v_3288 : Mem) => do
      v_9986 <- evaluateAddress v_3288;
      v_9987 <- getRegister v_3289;
      v_9991 <- load v_9986 8;
      v_9993 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9987 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_9991));
      v_9994 <- eval (extract v_9993 1 65);
      store v_9986 v_9994 8;
      v_9997 <- eval (isBitSet v_9993 1);
      v_10002 <- eval (eq (bv_xor (extract v_9987 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9987 v_9991) 59) (isBitSet v_9993 60)));
      setRegister cf (isBitClear v_9993 0);
      setRegister of (bit_and (eq v_10002 (isBitSet v_9991 0)) (notBool_ (eq v_10002 v_9997)));
      setRegister pf (parityFlag (extract v_9993 57 65));
      setRegister sf v_9997;
      setRegister zf (zeroFlag v_9994);
      pure ()
    pat_end

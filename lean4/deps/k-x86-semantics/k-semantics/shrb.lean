def shrb1 : instruction :=
  definst "shrb" $ do
    pattern fun (_ : clReg) (v_2977 : reg (bv 8)) => do
      v_4955 <- getRegister rcx;
      v_4957 <- eval (bv_and (extract v_4955 56 64) (expression.bv_nat 8 31));
      v_4958 <- eval (eq v_4957 (expression.bv_nat 8 0));
      v_4959 <- getRegister zf;
      v_4960 <- getRegister v_2977;
      v_4963 <- eval (lshr (concat v_4960 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_4957));
      v_4964 <- eval (extract v_4963 0 8);
      v_4967 <- getRegister sf;
      v_4970 <- getRegister pf;
      v_4975 <- getRegister of;
      v_4979 <- getRegister cf;
      v_4983 <- getRegister af;
      setRegister (lhs.of_reg v_2977) v_4964;
      setRegister af (mux v_4958 v_4983 undef);
      setRegister cf (mux (uge v_4957 (expression.bv_nat 8 8)) undef (mux v_4958 v_4979 (isBitSet v_4963 8)));
      setRegister of (mux (eq v_4957 (expression.bv_nat 8 1)) (isBitSet v_4960 0) (mux v_4958 v_4975 undef));
      setRegister pf (mux v_4958 v_4970 (parityFlag v_4964));
      setRegister sf (mux v_4958 v_4967 (isBitSet v_4963 0));
      setRegister zf (mux v_4958 v_4959 (eq v_4964 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2981 : imm int) (v_2982 : reg (bv 8)) => do
      v_4993 <- eval (bv_and (handleImmediateWithSignExtend v_2981 8 8) (expression.bv_nat 8 31));
      v_4994 <- eval (eq v_4993 (expression.bv_nat 8 0));
      v_4995 <- getRegister zf;
      v_4996 <- getRegister v_2982;
      v_4999 <- eval (lshr (concat v_4996 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_4993));
      v_5000 <- eval (extract v_4999 0 8);
      v_5003 <- getRegister sf;
      v_5006 <- getRegister pf;
      v_5011 <- getRegister of;
      v_5015 <- getRegister cf;
      v_5019 <- getRegister af;
      setRegister (lhs.of_reg v_2982) v_5000;
      setRegister af (mux v_4994 v_5019 undef);
      setRegister cf (mux (uge v_4993 (expression.bv_nat 8 8)) undef (mux v_4994 v_5015 (isBitSet v_4999 8)));
      setRegister of (mux (eq v_4993 (expression.bv_nat 8 1)) (isBitSet v_4996 0) (mux v_4994 v_5011 undef));
      setRegister pf (mux v_4994 v_5006 (parityFlag v_5000));
      setRegister sf (mux v_4994 v_5003 (isBitSet v_4999 0));
      setRegister zf (mux v_4994 v_4995 (eq v_5000 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2986 : reg (bv 8)) => do
      v_6489 <- getRegister v_2986;
      v_6491 <- eval (lshr (concat v_6489 (expression.bv_nat 1 0)) (expression.bv_nat 9 1));
      v_6492 <- eval (extract v_6491 0 8);
      setRegister (lhs.of_reg v_2986) v_6492;
      setRegister af undef;
      setRegister cf (isBitSet v_6491 8);
      setRegister of (isBitSet v_6489 0);
      setRegister pf (parityFlag v_6492);
      setRegister sf (isBitSet v_6491 0);
      setRegister zf (zeroFlag v_6492);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2948 : Mem) => do
      v_9314 <- evaluateAddress v_2948;
      v_9315 <- load v_9314 1;
      v_9317 <- getRegister rcx;
      v_9319 <- eval (bv_and (extract v_9317 56 64) (expression.bv_nat 8 31));
      v_9321 <- eval (lshr (concat v_9315 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_9319));
      v_9322 <- eval (extract v_9321 0 8);
      store v_9314 v_9322 1;
      v_9324 <- eval (eq v_9319 (expression.bv_nat 8 0));
      v_9325 <- getRegister zf;
      v_9328 <- getRegister sf;
      v_9331 <- getRegister pf;
      v_9336 <- getRegister of;
      v_9340 <- getRegister cf;
      v_9344 <- getRegister af;
      setRegister af (mux v_9324 v_9344 undef);
      setRegister cf (mux (uge v_9319 (expression.bv_nat 8 8)) undef (mux v_9324 v_9340 (isBitSet v_9321 8)));
      setRegister of (mux (eq v_9319 (expression.bv_nat 8 1)) (isBitSet v_9315 0) (mux v_9324 v_9336 undef));
      setRegister pf (mux v_9324 v_9331 (parityFlag v_9322));
      setRegister sf (mux v_9324 v_9328 (isBitSet v_9321 0));
      setRegister zf (mux v_9324 v_9325 (eq v_9322 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2952 : imm int) (v_2951 : Mem) => do
      v_9352 <- evaluateAddress v_2951;
      v_9353 <- load v_9352 1;
      v_9356 <- eval (bv_and (handleImmediateWithSignExtend v_2952 8 8) (expression.bv_nat 8 31));
      v_9358 <- eval (lshr (concat v_9353 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_9356));
      v_9359 <- eval (extract v_9358 0 8);
      store v_9352 v_9359 1;
      v_9361 <- eval (eq v_9356 (expression.bv_nat 8 0));
      v_9362 <- getRegister zf;
      v_9365 <- getRegister sf;
      v_9368 <- getRegister pf;
      v_9373 <- getRegister of;
      v_9377 <- getRegister cf;
      v_9381 <- getRegister af;
      setRegister af (mux v_9361 v_9381 undef);
      setRegister cf (mux (uge v_9356 (expression.bv_nat 8 8)) undef (mux v_9361 v_9377 (isBitSet v_9358 8)));
      setRegister of (mux (eq v_9356 (expression.bv_nat 8 1)) (isBitSet v_9353 0) (mux v_9361 v_9373 undef));
      setRegister pf (mux v_9361 v_9368 (parityFlag v_9359));
      setRegister sf (mux v_9361 v_9365 (isBitSet v_9358 0));
      setRegister zf (mux v_9361 v_9362 (eq v_9359 (expression.bv_nat 8 0)));
      pure ()
    pat_end;
    pattern fun (v_2955 : Mem) => do
      v_10088 <- evaluateAddress v_2955;
      v_10089 <- load v_10088 1;
      v_10091 <- eval (lshr (concat v_10089 (expression.bv_nat 1 0)) (expression.bv_nat 9 1));
      v_10092 <- eval (extract v_10091 0 8);
      store v_10088 v_10092 1;
      setRegister af undef;
      setRegister cf (isBitSet v_10091 8);
      setRegister of (isBitSet v_10089 0);
      setRegister pf (parityFlag v_10092);
      setRegister sf (isBitSet v_10091 0);
      setRegister zf (zeroFlag v_10092);
      pure ()
    pat_end

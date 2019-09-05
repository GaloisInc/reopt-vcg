def shrb1 : instruction :=
  definst "shrb" $ do
    pattern fun cl (v_2950 : reg (bv 8)) => do
      v_5308 <- getRegister rcx;
      v_5310 <- eval (bv_and (extract v_5308 56 64) (expression.bv_nat 8 31));
      v_5311 <- eval (eq v_5310 (expression.bv_nat 8 0));
      v_5312 <- eval (notBool_ v_5311);
      v_5313 <- getRegister v_2950;
      v_5316 <- eval (lshr (concat v_5313 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_5310));
      v_5317 <- eval (extract v_5316 0 8);
      v_5320 <- getRegister zf;
      v_5326 <- getRegister sf;
      v_5332 <- getRegister pf;
      v_5336 <- eval (eq v_5310 (expression.bv_nat 8 1));
      v_5340 <- eval (bit_and v_5312 undef);
      v_5341 <- getRegister of;
      v_5347 <- eval (uge v_5310 (expression.bv_nat 8 8));
      v_5352 <- getRegister cf;
      v_5358 <- getRegister af;
      setRegister (lhs.of_reg v_2950) v_5317;
      setRegister af (bit_or v_5340 (bit_and v_5311 (eq v_5358 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_5347 undef) (bit_and (notBool_ v_5347) (bit_or (bit_and v_5312 (isBitSet v_5316 8)) (bit_and v_5311 (eq v_5352 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_5336 (isBitSet v_5313 0)) (bit_and (notBool_ v_5336) (bit_or v_5340 (bit_and v_5311 (eq v_5341 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5312 (parityFlag v_5317)) (bit_and v_5311 (eq v_5332 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5312 (isBitSet v_5316 0)) (bit_and v_5311 (eq v_5326 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5312 (eq v_5317 (expression.bv_nat 8 0))) (bit_and v_5311 (eq v_5320 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2953 : imm int) (v_2955 : reg (bv 8)) => do
      v_5370 <- eval (bv_and (handleImmediateWithSignExtend v_2953 8 8) (expression.bv_nat 8 31));
      v_5371 <- eval (eq v_5370 (expression.bv_nat 8 0));
      v_5372 <- eval (notBool_ v_5371);
      v_5373 <- getRegister v_2955;
      v_5376 <- eval (lshr (concat v_5373 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_5370));
      v_5377 <- eval (extract v_5376 0 8);
      v_5380 <- getRegister zf;
      v_5386 <- getRegister sf;
      v_5392 <- getRegister pf;
      v_5396 <- eval (eq v_5370 (expression.bv_nat 8 1));
      v_5400 <- eval (bit_and v_5372 undef);
      v_5401 <- getRegister of;
      v_5407 <- eval (uge v_5370 (expression.bv_nat 8 8));
      v_5412 <- getRegister cf;
      v_5418 <- getRegister af;
      setRegister (lhs.of_reg v_2955) v_5377;
      setRegister af (bit_or v_5400 (bit_and v_5371 (eq v_5418 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_5407 undef) (bit_and (notBool_ v_5407) (bit_or (bit_and v_5372 (isBitSet v_5376 8)) (bit_and v_5371 (eq v_5412 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_5396 (isBitSet v_5373 0)) (bit_and (notBool_ v_5396) (bit_or v_5400 (bit_and v_5371 (eq v_5401 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5372 (parityFlag v_5377)) (bit_and v_5371 (eq v_5392 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5372 (isBitSet v_5376 0)) (bit_and v_5371 (eq v_5386 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5372 (eq v_5377 (expression.bv_nat 8 0))) (bit_and v_5371 (eq v_5380 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2958 : reg (bv 8)) => do
      v_7050 <- getRegister v_2958;
      v_7052 <- eval (lshr (concat v_7050 (expression.bv_nat 1 0)) (expression.bv_nat 9 1));
      v_7053 <- eval (extract v_7052 0 8);
      setRegister (lhs.of_reg v_2958) v_7053;
      setRegister af undef;
      setRegister cf (isBitSet v_7052 8);
      setRegister of (isBitSet v_7050 0);
      setRegister pf (parityFlag v_7053);
      setRegister sf (isBitSet v_7052 0);
      setRegister zf (zeroFlag v_7053);
      pure ()
    pat_end;
    pattern fun cl (v_2920 : Mem) => do
      v_10118 <- evaluateAddress v_2920;
      v_10119 <- load v_10118 1;
      v_10121 <- getRegister rcx;
      v_10123 <- eval (bv_and (extract v_10121 56 64) (expression.bv_nat 8 31));
      v_10125 <- eval (lshr (concat v_10119 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_10123));
      v_10126 <- eval (extract v_10125 0 8);
      store v_10118 v_10126 1;
      v_10128 <- eval (eq v_10123 (expression.bv_nat 8 0));
      v_10129 <- eval (notBool_ v_10128);
      v_10132 <- getRegister zf;
      v_10138 <- getRegister sf;
      v_10144 <- getRegister pf;
      v_10148 <- eval (eq v_10123 (expression.bv_nat 8 1));
      v_10152 <- eval (bit_and v_10129 undef);
      v_10153 <- getRegister of;
      v_10159 <- eval (uge v_10123 (expression.bv_nat 8 8));
      v_10164 <- getRegister cf;
      v_10170 <- getRegister af;
      setRegister af (bit_or v_10152 (bit_and v_10128 (eq v_10170 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_10159 undef) (bit_and (notBool_ v_10159) (bit_or (bit_and v_10129 (isBitSet v_10125 8)) (bit_and v_10128 (eq v_10164 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_10148 (isBitSet v_10119 0)) (bit_and (notBool_ v_10148) (bit_or v_10152 (bit_and v_10128 (eq v_10153 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10129 (parityFlag v_10126)) (bit_and v_10128 (eq v_10144 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10129 (isBitSet v_10125 0)) (bit_and v_10128 (eq v_10138 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10129 (eq v_10126 (expression.bv_nat 8 0))) (bit_and v_10128 (eq v_10132 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2924 : imm int) (v_2923 : Mem) => do
      v_10180 <- evaluateAddress v_2923;
      v_10181 <- load v_10180 1;
      v_10184 <- eval (bv_and (handleImmediateWithSignExtend v_2924 8 8) (expression.bv_nat 8 31));
      v_10186 <- eval (lshr (concat v_10181 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_10184));
      v_10187 <- eval (extract v_10186 0 8);
      store v_10180 v_10187 1;
      v_10189 <- eval (eq v_10184 (expression.bv_nat 8 0));
      v_10190 <- eval (notBool_ v_10189);
      v_10193 <- getRegister zf;
      v_10199 <- getRegister sf;
      v_10205 <- getRegister pf;
      v_10209 <- eval (eq v_10184 (expression.bv_nat 8 1));
      v_10213 <- eval (bit_and v_10190 undef);
      v_10214 <- getRegister of;
      v_10220 <- eval (uge v_10184 (expression.bv_nat 8 8));
      v_10225 <- getRegister cf;
      v_10231 <- getRegister af;
      setRegister af (bit_or v_10213 (bit_and v_10189 (eq v_10231 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_10220 undef) (bit_and (notBool_ v_10220) (bit_or (bit_and v_10190 (isBitSet v_10186 8)) (bit_and v_10189 (eq v_10225 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_10209 (isBitSet v_10181 0)) (bit_and (notBool_ v_10209) (bit_or v_10213 (bit_and v_10189 (eq v_10214 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10190 (parityFlag v_10187)) (bit_and v_10189 (eq v_10205 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10190 (isBitSet v_10186 0)) (bit_and v_10189 (eq v_10199 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10190 (eq v_10187 (expression.bv_nat 8 0))) (bit_and v_10189 (eq v_10193 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2927 : Mem) => do
      v_11093 <- evaluateAddress v_2927;
      v_11094 <- load v_11093 1;
      v_11096 <- eval (lshr (concat v_11094 (expression.bv_nat 1 0)) (expression.bv_nat 9 1));
      v_11097 <- eval (extract v_11096 0 8);
      store v_11093 v_11097 1;
      setRegister af undef;
      setRegister cf (isBitSet v_11096 8);
      setRegister of (isBitSet v_11094 0);
      setRegister pf (parityFlag v_11097);
      setRegister sf (isBitSet v_11096 0);
      setRegister zf (zeroFlag v_11097);
      pure ()
    pat_end

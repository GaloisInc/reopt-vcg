def shrl1 : instruction :=
  definst "shrl" $ do
    pattern fun cl (v_2979 : reg (bv 32)) => do
      v_5464 <- getRegister rcx;
      v_5466 <- eval (bv_and (extract v_5464 56 64) (expression.bv_nat 8 31));
      v_5467 <- eval (eq v_5466 (expression.bv_nat 8 0));
      v_5468 <- eval (notBool_ v_5467);
      v_5469 <- getRegister v_2979;
      v_5472 <- eval (lshr (concat v_5469 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_5466));
      v_5473 <- eval (extract v_5472 0 32);
      v_5476 <- getRegister zf;
      v_5482 <- getRegister sf;
      v_5489 <- getRegister pf;
      v_5493 <- eval (eq v_5466 (expression.bv_nat 8 1));
      v_5497 <- eval (bit_and v_5468 undef);
      v_5498 <- getRegister of;
      v_5504 <- eval (uge v_5466 (expression.bv_nat 8 32));
      v_5509 <- getRegister cf;
      v_5515 <- getRegister af;
      setRegister (lhs.of_reg v_2979) v_5473;
      setRegister af (bit_or v_5497 (bit_and v_5467 (eq v_5515 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_5504 undef) (bit_and (notBool_ v_5504) (bit_or (bit_and v_5468 (isBitSet v_5472 32)) (bit_and v_5467 (eq v_5509 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_5493 (isBitSet v_5469 0)) (bit_and (notBool_ v_5493) (bit_or v_5497 (bit_and v_5467 (eq v_5498 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5468 (parityFlag (extract v_5472 24 32))) (bit_and v_5467 (eq v_5489 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5468 (isBitSet v_5472 0)) (bit_and v_5467 (eq v_5482 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5468 (eq v_5473 (expression.bv_nat 32 0))) (bit_and v_5467 (eq v_5476 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2982 : imm int) (v_2984 : reg (bv 32)) => do
      v_5527 <- eval (bv_and (handleImmediateWithSignExtend v_2982 8 8) (expression.bv_nat 8 31));
      v_5528 <- eval (eq v_5527 (expression.bv_nat 8 0));
      v_5529 <- eval (notBool_ v_5528);
      v_5530 <- getRegister v_2984;
      v_5533 <- eval (lshr (concat v_5530 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_5527));
      v_5534 <- eval (extract v_5533 0 32);
      v_5537 <- getRegister zf;
      v_5543 <- getRegister sf;
      v_5550 <- getRegister pf;
      v_5554 <- eval (eq v_5527 (expression.bv_nat 8 1));
      v_5558 <- eval (bit_and v_5529 undef);
      v_5559 <- getRegister of;
      v_5565 <- eval (uge v_5527 (expression.bv_nat 8 32));
      v_5570 <- getRegister cf;
      v_5576 <- getRegister af;
      setRegister (lhs.of_reg v_2984) v_5534;
      setRegister af (bit_or v_5558 (bit_and v_5528 (eq v_5576 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_5565 undef) (bit_and (notBool_ v_5565) (bit_or (bit_and v_5529 (isBitSet v_5533 32)) (bit_and v_5528 (eq v_5570 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_5554 (isBitSet v_5530 0)) (bit_and (notBool_ v_5554) (bit_or v_5558 (bit_and v_5528 (eq v_5559 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_5529 (parityFlag (extract v_5533 24 32))) (bit_and v_5528 (eq v_5550 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_5529 (isBitSet v_5533 0)) (bit_and v_5528 (eq v_5543 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_5529 (eq v_5534 (expression.bv_nat 32 0))) (bit_and v_5528 (eq v_5537 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2987 : reg (bv 32)) => do
      v_7095 <- getRegister v_2987;
      v_7097 <- eval (lshr (concat v_7095 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      v_7098 <- eval (extract v_7097 0 32);
      setRegister (lhs.of_reg v_2987) v_7098;
      setRegister af undef;
      setRegister cf (isBitSet v_7097 32);
      setRegister of (isBitSet v_7095 0);
      setRegister pf (parityFlag (extract v_7097 24 32));
      setRegister sf (isBitSet v_7097 0);
      setRegister zf (zeroFlag v_7098);
      pure ()
    pat_end;
    pattern fun cl (v_2965 : Mem) => do
      v_10276 <- evaluateAddress v_2965;
      v_10277 <- load v_10276 4;
      v_10279 <- getRegister rcx;
      v_10281 <- eval (bv_and (extract v_10279 56 64) (expression.bv_nat 8 31));
      v_10283 <- eval (lshr (concat v_10277 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_10281));
      v_10284 <- eval (extract v_10283 0 32);
      store v_10276 v_10284 4;
      v_10286 <- eval (eq v_10281 (expression.bv_nat 8 0));
      v_10287 <- eval (notBool_ v_10286);
      v_10290 <- getRegister zf;
      v_10296 <- getRegister sf;
      v_10303 <- getRegister pf;
      v_10307 <- eval (eq v_10281 (expression.bv_nat 8 1));
      v_10311 <- eval (bit_and v_10287 undef);
      v_10312 <- getRegister of;
      v_10318 <- eval (uge v_10281 (expression.bv_nat 8 32));
      v_10323 <- getRegister cf;
      v_10329 <- getRegister af;
      setRegister af (bit_or v_10311 (bit_and v_10286 (eq v_10329 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_10318 undef) (bit_and (notBool_ v_10318) (bit_or (bit_and v_10287 (isBitSet v_10283 32)) (bit_and v_10286 (eq v_10323 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_10307 (isBitSet v_10277 0)) (bit_and (notBool_ v_10307) (bit_or v_10311 (bit_and v_10286 (eq v_10312 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10287 (parityFlag (extract v_10283 24 32))) (bit_and v_10286 (eq v_10303 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10287 (isBitSet v_10283 0)) (bit_and v_10286 (eq v_10296 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10287 (eq v_10284 (expression.bv_nat 32 0))) (bit_and v_10286 (eq v_10290 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2969 : imm int) (v_2968 : Mem) => do
      v_10339 <- evaluateAddress v_2968;
      v_10340 <- load v_10339 4;
      v_10343 <- eval (bv_and (handleImmediateWithSignExtend v_2969 8 8) (expression.bv_nat 8 31));
      v_10345 <- eval (lshr (concat v_10340 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_10343));
      v_10346 <- eval (extract v_10345 0 32);
      store v_10339 v_10346 4;
      v_10348 <- eval (eq v_10343 (expression.bv_nat 8 0));
      v_10349 <- eval (notBool_ v_10348);
      v_10352 <- getRegister zf;
      v_10358 <- getRegister sf;
      v_10365 <- getRegister pf;
      v_10369 <- eval (eq v_10343 (expression.bv_nat 8 1));
      v_10373 <- eval (bit_and v_10349 undef);
      v_10374 <- getRegister of;
      v_10380 <- eval (uge v_10343 (expression.bv_nat 8 32));
      v_10385 <- getRegister cf;
      v_10391 <- getRegister af;
      setRegister af (bit_or v_10373 (bit_and v_10348 (eq v_10391 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_10380 undef) (bit_and (notBool_ v_10380) (bit_or (bit_and v_10349 (isBitSet v_10345 32)) (bit_and v_10348 (eq v_10385 (expression.bv_nat 1 1))))));
      setRegister of (bit_or (bit_and v_10369 (isBitSet v_10340 0)) (bit_and (notBool_ v_10369) (bit_or v_10373 (bit_and v_10348 (eq v_10374 (expression.bv_nat 1 1))))));
      setRegister pf (bit_or (bit_and v_10349 (parityFlag (extract v_10345 24 32))) (bit_and v_10348 (eq v_10365 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_10349 (isBitSet v_10345 0)) (bit_and v_10348 (eq v_10358 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_10349 (eq v_10346 (expression.bv_nat 32 0))) (bit_and v_10348 (eq v_10352 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_2972 : Mem) => do
      v_11110 <- evaluateAddress v_2972;
      v_11111 <- load v_11110 4;
      v_11113 <- eval (lshr (concat v_11111 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      v_11114 <- eval (extract v_11113 0 32);
      store v_11110 v_11114 4;
      setRegister af undef;
      setRegister cf (isBitSet v_11113 32);
      setRegister of (isBitSet v_11111 0);
      setRegister pf (parityFlag (extract v_11113 24 32));
      setRegister sf (isBitSet v_11113 0);
      setRegister zf (zeroFlag v_11114);
      pure ()
    pat_end

def sbbq1 : instruction :=
  definst "sbbq" $ do
    pattern fun (v_3326 : imm int) (v_3325 : reg (bv 64)) => do
      v_7521 <- getRegister cf;
      v_7523 <- eval (handleImmediateWithSignExtend v_3326 32 32);
      v_7524 <- eval (sext v_7523 64);
      v_7526 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_7524 (expression.bv_nat 64 18446744073709551615)));
      v_7529 <- getRegister v_3325;
      v_7531 <- eval (add (mux (eq v_7521 (expression.bv_nat 1 1)) v_7526 (add v_7526 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_7529));
      v_7532 <- eval (extract v_7531 1 65);
      v_7534 <- eval (isBitSet v_7531 1);
      v_7539 <- eval (eq (bv_xor (extract v_7524 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3325) v_7532;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_7523 27) (isBitSet v_7529 59))) (isBitSet v_7531 60)));
      setRegister cf (notBool_ (isBitSet v_7531 0));
      setRegister of (bit_and (eq v_7539 (isBitSet v_7529 0)) (notBool_ (eq v_7539 v_7534)));
      setRegister pf (parityFlag (extract v_7531 57 65));
      setRegister sf v_7534;
      setRegister zf (zeroFlag v_7532);
      pure ()
    pat_end;
    pattern fun (v_3334 : reg (bv 64)) (v_3335 : reg (bv 64)) => do
      v_7565 <- getRegister cf;
      v_7567 <- getRegister v_3334;
      v_7569 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_7567 (expression.bv_nat 64 18446744073709551615)));
      v_7572 <- getRegister v_3335;
      v_7574 <- eval (add (mux (eq v_7565 (expression.bv_nat 1 1)) v_7569 (add v_7569 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_7572));
      v_7575 <- eval (extract v_7574 1 65);
      v_7577 <- eval (isBitSet v_7574 1);
      v_7582 <- eval (eq (bv_xor (extract v_7567 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3335) v_7575;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7567 v_7572) 59) (isBitSet v_7574 60)));
      setRegister cf (notBool_ (isBitSet v_7574 0));
      setRegister of (bit_and (eq v_7582 (isBitSet v_7572 0)) (notBool_ (eq v_7582 v_7577)));
      setRegister pf (parityFlag (extract v_7574 57 65));
      setRegister sf v_7577;
      setRegister zf (zeroFlag v_7575);
      pure ()
    pat_end;
    pattern fun (v_3329 : Mem) (v_3330 : reg (bv 64)) => do
      v_11548 <- getRegister cf;
      v_11550 <- evaluateAddress v_3329;
      v_11551 <- load v_11550 8;
      v_11553 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_11551 (expression.bv_nat 64 18446744073709551615)));
      v_11556 <- getRegister v_3330;
      v_11558 <- eval (add (mux (eq v_11548 (expression.bv_nat 1 1)) v_11553 (add v_11553 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_11556));
      v_11559 <- eval (extract v_11558 1 65);
      v_11561 <- eval (isBitSet v_11558 1);
      v_11566 <- eval (eq (bv_xor (extract v_11551 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3330) v_11559;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_11551 v_11556) 59) (isBitSet v_11558 60)));
      setRegister cf (notBool_ (isBitSet v_11558 0));
      setRegister of (bit_and (eq v_11566 (isBitSet v_11556 0)) (notBool_ (eq v_11566 v_11561)));
      setRegister pf (parityFlag (extract v_11558 57 65));
      setRegister sf v_11561;
      setRegister zf (zeroFlag v_11559);
      pure ()
    pat_end;
    pattern fun (v_3317 : imm int) (v_3316 : Mem) => do
      v_14326 <- evaluateAddress v_3316;
      v_14327 <- getRegister cf;
      v_14329 <- eval (handleImmediateWithSignExtend v_3317 32 32);
      v_14330 <- eval (sext v_14329 64);
      v_14332 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_14330 (expression.bv_nat 64 18446744073709551615)));
      v_14335 <- load v_14326 8;
      v_14337 <- eval (add (mux (eq v_14327 (expression.bv_nat 1 1)) v_14332 (add v_14332 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_14335));
      v_14338 <- eval (extract v_14337 1 65);
      store v_14326 v_14338 8;
      v_14341 <- eval (isBitSet v_14337 1);
      v_14346 <- eval (eq (bv_xor (extract v_14330 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_14329 27) (isBitSet v_14335 59))) (isBitSet v_14337 60)));
      setRegister cf (notBool_ (isBitSet v_14337 0));
      setRegister of (bit_and (eq v_14346 (isBitSet v_14335 0)) (notBool_ (eq v_14346 v_14341)));
      setRegister pf (parityFlag (extract v_14337 57 65));
      setRegister sf v_14341;
      setRegister zf (zeroFlag v_14338);
      pure ()
    pat_end;
    pattern fun (v_3321 : reg (bv 64)) (v_3320 : Mem) => do
      v_14367 <- evaluateAddress v_3320;
      v_14368 <- getRegister cf;
      v_14370 <- getRegister v_3321;
      v_14372 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_14370 (expression.bv_nat 64 18446744073709551615)));
      v_14375 <- load v_14367 8;
      v_14377 <- eval (add (mux (eq v_14368 (expression.bv_nat 1 1)) v_14372 (add v_14372 (expression.bv_nat 65 1))) (concat (expression.bv_nat 1 0) v_14375));
      v_14378 <- eval (extract v_14377 1 65);
      store v_14367 v_14378 8;
      v_14381 <- eval (isBitSet v_14377 1);
      v_14386 <- eval (eq (bv_xor (extract v_14370 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_14370 v_14375) 59) (isBitSet v_14377 60)));
      setRegister cf (notBool_ (isBitSet v_14377 0));
      setRegister of (bit_and (eq v_14386 (isBitSet v_14375 0)) (notBool_ (eq v_14386 v_14381)));
      setRegister pf (parityFlag (extract v_14377 57 65));
      setRegister sf v_14381;
      setRegister zf (zeroFlag v_14378);
      pure ()
    pat_end

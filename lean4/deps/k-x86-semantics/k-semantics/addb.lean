def addb1 : instruction :=
  definst "addb" $ do
    pattern fun (v_2610 : imm int) (v_2613 : reg (bv 8)) => do
      v_4547 <- eval (handleImmediateWithSignExtend v_2610 8 8);
      v_4549 <- getRegister v_2613;
      v_4551 <- eval (add (concat (expression.bv_nat 1 0) v_4547) (concat (expression.bv_nat 1 0) v_4549));
      v_4552 <- eval (extract v_4551 1 9);
      v_4554 <- eval (isBitSet v_4551 1);
      v_4556 <- eval (isBitSet v_4547 0);
      setRegister (lhs.of_reg v_2613) v_4552;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4547 v_4549) 3) (isBitSet v_4551 4)));
      setRegister cf (isBitSet v_4551 0);
      setRegister of (bit_and (eq v_4556 (isBitSet v_4549 0)) (notBool_ (eq v_4556 v_4554)));
      setRegister pf (parityFlag v_4552);
      setRegister sf v_4554;
      setRegister zf (zeroFlag v_4552);
      pure ()
    pat_end;
    pattern fun (v_2626 : reg (bv 8)) (v_2627 : reg (bv 8)) => do
      v_4607 <- getRegister v_2626;
      v_4609 <- getRegister v_2627;
      v_4611 <- eval (add (concat (expression.bv_nat 1 0) v_4607) (concat (expression.bv_nat 1 0) v_4609));
      v_4612 <- eval (extract v_4611 1 9);
      v_4614 <- eval (isBitSet v_4611 1);
      v_4616 <- eval (isBitSet v_4607 0);
      setRegister (lhs.of_reg v_2627) v_4612;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4607 v_4609) 3) (isBitSet v_4611 4)));
      setRegister cf (isBitSet v_4611 0);
      setRegister of (bit_and (eq v_4616 (isBitSet v_4609 0)) (notBool_ (eq v_4616 v_4614)));
      setRegister pf (parityFlag v_4612);
      setRegister sf v_4614;
      setRegister zf (zeroFlag v_4612);
      pure ()
    pat_end;
    pattern fun (v_2616 : Mem) (v_2617 : reg (bv 8)) => do
      v_8855 <- evaluateAddress v_2616;
      v_8856 <- load v_8855 1;
      v_8858 <- getRegister v_2617;
      v_8860 <- eval (add (concat (expression.bv_nat 1 0) v_8856) (concat (expression.bv_nat 1 0) v_8858));
      v_8861 <- eval (extract v_8860 1 9);
      v_8863 <- eval (isBitSet v_8860 1);
      v_8865 <- eval (isBitSet v_8856 0);
      setRegister (lhs.of_reg v_2617) v_8861;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8856 v_8858) 3) (isBitSet v_8860 4)));
      setRegister cf (isBitSet v_8860 0);
      setRegister of (bit_and (eq v_8865 (isBitSet v_8858 0)) (notBool_ (eq v_8865 v_8863)));
      setRegister pf (parityFlag v_8861);
      setRegister sf v_8863;
      setRegister zf (zeroFlag v_8861);
      pure ()
    pat_end;
    pattern fun (v_2579 : imm int) (v_2581 : Mem) => do
      v_10290 <- evaluateAddress v_2581;
      v_10291 <- eval (handleImmediateWithSignExtend v_2579 8 8);
      v_10293 <- load v_10290 1;
      v_10295 <- eval (add (concat (expression.bv_nat 1 0) v_10291) (concat (expression.bv_nat 1 0) v_10293));
      v_10296 <- eval (extract v_10295 1 9);
      store v_10290 v_10296 1;
      v_10299 <- eval (isBitSet v_10295 1);
      v_10301 <- eval (isBitSet v_10291 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10291 v_10293) 3) (isBitSet v_10295 4)));
      setRegister cf (isBitSet v_10295 0);
      setRegister of (bit_and (eq v_10301 (isBitSet v_10293 0)) (notBool_ (eq v_10301 v_10299)));
      setRegister pf (parityFlag v_10296);
      setRegister sf v_10299;
      setRegister zf (zeroFlag v_10296);
      pure ()
    pat_end;
    pattern fun (v_2589 : reg (bv 8)) (v_2588 : Mem) => do
      v_10348 <- evaluateAddress v_2588;
      v_10349 <- getRegister v_2589;
      v_10351 <- load v_10348 1;
      v_10353 <- eval (add (concat (expression.bv_nat 1 0) v_10349) (concat (expression.bv_nat 1 0) v_10351));
      v_10354 <- eval (extract v_10353 1 9);
      store v_10348 v_10354 1;
      v_10357 <- eval (isBitSet v_10353 1);
      v_10359 <- eval (isBitSet v_10349 0);
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10349 v_10351) 3) (isBitSet v_10353 4)));
      setRegister cf (isBitSet v_10353 0);
      setRegister of (bit_and (eq v_10359 (isBitSet v_10351 0)) (notBool_ (eq v_10359 v_10357)));
      setRegister pf (parityFlag v_10354);
      setRegister sf v_10357;
      setRegister zf (zeroFlag v_10354);
      pure ()
    pat_end

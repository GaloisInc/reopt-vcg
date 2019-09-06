def cmpl1 : instruction :=
  definst "cmpl" $ do
    pattern fun (v_3456 : imm int) (v_3460 : reg (bv 32)) => do
      v_5435 <- eval (handleImmediateWithSignExtend v_3456 32 32);
      v_5439 <- getRegister v_3460;
      v_5441 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5435 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5439));
      v_5444 <- eval (isBitSet v_5441 1);
      v_5449 <- eval (eq (bv_xor (extract v_5435 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5435 v_5439) 27) (isBitSet v_5441 28)));
      setRegister cf (isBitClear v_5441 0);
      setRegister of (bit_and (eq v_5449 (isBitSet v_5439 0)) (notBool_ (eq v_5449 v_5444)));
      setRegister pf (parityFlag (extract v_5441 25 33));
      setRegister sf v_5444;
      setRegister zf (zeroFlag (extract v_5441 1 33));
      pure ()
    pat_end;
    pattern fun (v_3468 : reg (bv 32)) (v_3469 : reg (bv 32)) => do
      v_5471 <- getRegister v_3468;
      v_5475 <- getRegister v_3469;
      v_5477 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5471 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5475));
      v_5480 <- eval (isBitSet v_5477 1);
      v_5485 <- eval (eq (bv_xor (extract v_5471 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5471 v_5475) 27) (isBitSet v_5477 28)));
      setRegister cf (isBitClear v_5477 0);
      setRegister of (bit_and (eq v_5485 (isBitSet v_5475 0)) (notBool_ (eq v_5485 v_5480)));
      setRegister pf (parityFlag (extract v_5477 25 33));
      setRegister sf v_5480;
      setRegister zf (zeroFlag (extract v_5477 1 33));
      pure ()
    pat_end;
    pattern fun (v_3449 : imm int) (v_3448 : Mem) => do
      v_8508 <- eval (handleImmediateWithSignExtend v_3449 32 32);
      v_8512 <- evaluateAddress v_3448;
      v_8513 <- load v_8512 4;
      v_8515 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8508 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8513));
      v_8518 <- eval (isBitSet v_8515 1);
      v_8523 <- eval (eq (bv_xor (extract v_8508 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8508 v_8513) 27) (isBitSet v_8515 28)));
      setRegister cf (isBitClear v_8515 0);
      setRegister of (bit_and (eq v_8523 (isBitSet v_8513 0)) (notBool_ (eq v_8523 v_8518)));
      setRegister pf (parityFlag (extract v_8515 25 33));
      setRegister sf v_8518;
      setRegister zf (zeroFlag (extract v_8515 1 33));
      pure ()
    pat_end;
    pattern fun (v_3455 : reg (bv 32)) (v_3452 : Mem) => do
      v_8541 <- getRegister v_3455;
      v_8545 <- evaluateAddress v_3452;
      v_8546 <- load v_8545 4;
      v_8548 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8541 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8546));
      v_8551 <- eval (isBitSet v_8548 1);
      v_8556 <- eval (eq (bv_xor (extract v_8541 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8541 v_8546) 27) (isBitSet v_8548 28)));
      setRegister cf (isBitClear v_8548 0);
      setRegister of (bit_and (eq v_8556 (isBitSet v_8546 0)) (notBool_ (eq v_8556 v_8551)));
      setRegister pf (parityFlag (extract v_8548 25 33));
      setRegister sf v_8551;
      setRegister zf (zeroFlag (extract v_8548 1 33));
      pure ()
    pat_end;
    pattern fun (v_3461 : Mem) (v_3464 : reg (bv 32)) => do
      v_8574 <- evaluateAddress v_3461;
      v_8575 <- load v_8574 4;
      v_8579 <- getRegister v_3464;
      v_8581 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8575 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8579));
      v_8584 <- eval (isBitSet v_8581 1);
      v_8589 <- eval (eq (bv_xor (extract v_8575 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8575 v_8579) 27) (isBitSet v_8581 28)));
      setRegister cf (isBitClear v_8581 0);
      setRegister of (bit_and (eq v_8589 (isBitSet v_8579 0)) (notBool_ (eq v_8589 v_8584)));
      setRegister pf (parityFlag (extract v_8581 25 33));
      setRegister sf v_8584;
      setRegister zf (zeroFlag (extract v_8581 1 33));
      pure ()
    pat_end

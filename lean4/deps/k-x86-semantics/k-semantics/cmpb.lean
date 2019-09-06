def cmpb1 : instruction :=
  definst "cmpb" $ do
    pattern fun (v_3425 : imm int) (v_3426 : reg (bv 8)) => do
      v_5295 <- eval (handleImmediateWithSignExtend v_3425 8 8);
      v_5299 <- getRegister v_3426;
      v_5301 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5295 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5299));
      v_5302 <- eval (extract v_5301 1 9);
      v_5304 <- eval (isBitSet v_5301 1);
      v_5308 <- eval (eq (bv_xor (extract v_5295 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5295 v_5299) 3) (isBitSet v_5301 4)));
      setRegister cf (isBitClear v_5301 0);
      setRegister of (bit_and (eq v_5308 (isBitSet v_5299 0)) (notBool_ (eq v_5308 v_5304)));
      setRegister pf (parityFlag v_5302);
      setRegister sf v_5304;
      setRegister zf (zeroFlag v_5302);
      pure ()
    pat_end;
    pattern fun (v_3439 : reg (bv 8)) (v_3440 : reg (bv 8)) => do
      v_5361 <- getRegister v_3439;
      v_5365 <- getRegister v_3440;
      v_5367 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5361 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5365));
      v_5368 <- eval (extract v_5367 1 9);
      v_5370 <- eval (isBitSet v_5367 1);
      v_5374 <- eval (eq (bv_xor (extract v_5361 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5361 v_5365) 3) (isBitSet v_5367 4)));
      setRegister cf (isBitClear v_5367 0);
      setRegister of (bit_and (eq v_5374 (isBitSet v_5365 0)) (notBool_ (eq v_5374 v_5370)));
      setRegister pf (parityFlag v_5368);
      setRegister sf v_5370;
      setRegister zf (zeroFlag v_5368);
      pure ()
    pat_end;
    pattern fun (v_3394 : imm int) (v_3395 : Mem) => do
      v_8348 <- eval (handleImmediateWithSignExtend v_3394 8 8);
      v_8352 <- evaluateAddress v_3395;
      v_8353 <- load v_8352 1;
      v_8355 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8348 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8353));
      v_8356 <- eval (extract v_8355 1 9);
      v_8358 <- eval (isBitSet v_8355 1);
      v_8362 <- eval (eq (bv_xor (extract v_8348 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8348 v_8353) 3) (isBitSet v_8355 4)));
      setRegister cf (isBitClear v_8355 0);
      setRegister of (bit_and (eq v_8362 (isBitSet v_8353 0)) (notBool_ (eq v_8362 v_8358)));
      setRegister pf (parityFlag v_8356);
      setRegister sf v_8358;
      setRegister zf (zeroFlag v_8356);
      pure ()
    pat_end;
    pattern fun (v_3403 : reg (bv 8)) (v_3402 : Mem) => do
      v_8412 <- getRegister v_3403;
      v_8416 <- evaluateAddress v_3402;
      v_8417 <- load v_8416 1;
      v_8419 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8412 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8417));
      v_8420 <- eval (extract v_8419 1 9);
      v_8422 <- eval (isBitSet v_8419 1);
      v_8426 <- eval (eq (bv_xor (extract v_8412 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8412 v_8417) 3) (isBitSet v_8419 4)));
      setRegister cf (isBitClear v_8419 0);
      setRegister of (bit_and (eq v_8426 (isBitSet v_8417 0)) (notBool_ (eq v_8426 v_8422)));
      setRegister pf (parityFlag v_8420);
      setRegister sf v_8422;
      setRegister zf (zeroFlag v_8420);
      pure ()
    pat_end;
    pattern fun (v_3430 : Mem) (v_3431 : reg (bv 8)) => do
      v_8476 <- evaluateAddress v_3430;
      v_8477 <- load v_8476 1;
      v_8481 <- getRegister v_3431;
      v_8483 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8477 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8481));
      v_8484 <- eval (extract v_8483 1 9);
      v_8486 <- eval (isBitSet v_8483 1);
      v_8490 <- eval (eq (bv_xor (extract v_8477 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8477 v_8481) 3) (isBitSet v_8483 4)));
      setRegister cf (isBitClear v_8483 0);
      setRegister of (bit_and (eq v_8490 (isBitSet v_8481 0)) (notBool_ (eq v_8490 v_8486)));
      setRegister pf (parityFlag v_8484);
      setRegister sf v_8486;
      setRegister zf (zeroFlag v_8484);
      pure ()
    pat_end

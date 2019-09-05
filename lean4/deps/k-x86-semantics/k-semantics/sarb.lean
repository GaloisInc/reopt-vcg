def sarb1 : instruction :=
  definst "sarb" $ do
    pattern fun cl (v_3092 : reg (bv 8)) => do
      v_6533 <- getRegister rcx;
      v_6535 <- eval (bv_and (extract v_6533 56 64) (expression.bv_nat 8 31));
      v_6536 <- eval (eq v_6535 (expression.bv_nat 8 0));
      v_6537 <- eval (notBool_ v_6536);
      v_6538 <- getRegister v_3092;
      v_6541 <- eval (ashr (concat v_6538 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_6535));
      v_6542 <- eval (extract v_6541 0 8);
      v_6545 <- getRegister zf;
      v_6551 <- getRegister sf;
      v_6557 <- getRegister pf;
      v_6563 <- eval (bit_and v_6537 undef);
      v_6564 <- getRegister of;
      v_6571 <- getRegister cf;
      v_6575 <- getRegister af;
      setRegister (lhs.of_reg v_3092) v_6542;
      setRegister af (bit_or v_6563 (bit_and v_6536 (eq v_6575 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_6537 (isBitSet v_6541 8)) (bit_and v_6536 (eq v_6571 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_6535 (expression.bv_nat 8 1))) (bit_or v_6563 (bit_and v_6536 (eq v_6564 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_6537 (parityFlag v_6542)) (bit_and v_6536 (eq v_6557 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6537 (isBitSet v_6541 0)) (bit_and v_6536 (eq v_6551 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6537 (eq v_6542 (expression.bv_nat 8 0))) (bit_and v_6536 (eq v_6545 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3095 : imm int) (v_3097 : reg (bv 8)) => do
      v_6587 <- eval (bv_and (handleImmediateWithSignExtend v_3095 8 8) (expression.bv_nat 8 31));
      v_6588 <- eval (eq v_6587 (expression.bv_nat 8 0));
      v_6589 <- eval (notBool_ v_6588);
      v_6590 <- getRegister v_3097;
      v_6593 <- eval (ashr (concat v_6590 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_6587));
      v_6594 <- eval (extract v_6593 0 8);
      v_6597 <- getRegister zf;
      v_6603 <- getRegister sf;
      v_6609 <- getRegister pf;
      v_6615 <- eval (bit_and v_6589 undef);
      v_6616 <- getRegister of;
      v_6623 <- getRegister cf;
      v_6627 <- getRegister af;
      setRegister (lhs.of_reg v_3097) v_6594;
      setRegister af (bit_or v_6615 (bit_and v_6588 (eq v_6627 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_6589 (isBitSet v_6593 8)) (bit_and v_6588 (eq v_6623 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_6587 (expression.bv_nat 8 1))) (bit_or v_6615 (bit_and v_6588 (eq v_6616 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_6589 (parityFlag v_6594)) (bit_and v_6588 (eq v_6609 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_6589 (isBitSet v_6593 0)) (bit_and v_6588 (eq v_6603 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_6589 (eq v_6594 (expression.bv_nat 8 0))) (bit_and v_6588 (eq v_6597 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3100 : reg (bv 8)) => do
      v_8424 <- getRegister v_3100;
      v_8426 <- eval (ashr (concat v_8424 (expression.bv_nat 1 0)) (expression.bv_nat 9 1));
      v_8427 <- eval (extract v_8426 0 8);
      setRegister (lhs.of_reg v_3100) v_8427;
      setRegister af undef;
      setRegister cf (isBitSet v_8426 8);
      setRegister of bit_zero;
      setRegister pf (parityFlag v_8427);
      setRegister sf (isBitSet v_8426 0);
      setRegister zf (zeroFlag v_8427);
      pure ()
    pat_end;
    pattern fun cl (v_3062 : Mem) => do
      v_13555 <- evaluateAddress v_3062;
      v_13556 <- load v_13555 1;
      v_13558 <- getRegister rcx;
      v_13560 <- eval (bv_and (extract v_13558 56 64) (expression.bv_nat 8 31));
      v_13562 <- eval (ashr (concat v_13556 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_13560));
      v_13563 <- eval (extract v_13562 0 8);
      store v_13555 v_13563 1;
      v_13565 <- eval (eq v_13560 (expression.bv_nat 8 0));
      v_13566 <- eval (notBool_ v_13565);
      v_13569 <- getRegister zf;
      v_13575 <- getRegister sf;
      v_13581 <- getRegister pf;
      v_13587 <- eval (bit_and v_13566 undef);
      v_13588 <- getRegister of;
      v_13595 <- getRegister cf;
      v_13599 <- getRegister af;
      setRegister af (bit_or v_13587 (bit_and v_13565 (eq v_13599 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_13566 (isBitSet v_13562 8)) (bit_and v_13565 (eq v_13595 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_13560 (expression.bv_nat 8 1))) (bit_or v_13587 (bit_and v_13565 (eq v_13588 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_13566 (parityFlag v_13563)) (bit_and v_13565 (eq v_13581 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13566 (isBitSet v_13562 0)) (bit_and v_13565 (eq v_13575 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13566 (eq v_13563 (expression.bv_nat 8 0))) (bit_and v_13565 (eq v_13569 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3065 : imm int) (v_3066 : Mem) => do
      v_13609 <- evaluateAddress v_3066;
      v_13610 <- load v_13609 1;
      v_13613 <- eval (bv_and (handleImmediateWithSignExtend v_3065 8 8) (expression.bv_nat 8 31));
      v_13615 <- eval (ashr (concat v_13610 (expression.bv_nat 1 0)) (concat (expression.bv_nat 1 0) v_13613));
      v_13616 <- eval (extract v_13615 0 8);
      store v_13609 v_13616 1;
      v_13618 <- eval (eq v_13613 (expression.bv_nat 8 0));
      v_13619 <- eval (notBool_ v_13618);
      v_13622 <- getRegister zf;
      v_13628 <- getRegister sf;
      v_13634 <- getRegister pf;
      v_13640 <- eval (bit_and v_13619 undef);
      v_13641 <- getRegister of;
      v_13648 <- getRegister cf;
      v_13652 <- getRegister af;
      setRegister af (bit_or v_13640 (bit_and v_13618 (eq v_13652 (expression.bv_nat 1 1))));
      setRegister cf (bit_or (bit_and v_13619 (isBitSet v_13615 8)) (bit_and v_13618 (eq v_13648 (expression.bv_nat 1 1))));
      setRegister of (bit_and (notBool_ (eq v_13613 (expression.bv_nat 8 1))) (bit_or v_13640 (bit_and v_13618 (eq v_13641 (expression.bv_nat 1 1)))));
      setRegister pf (bit_or (bit_and v_13619 (parityFlag v_13616)) (bit_and v_13618 (eq v_13634 (expression.bv_nat 1 1))));
      setRegister sf (bit_or (bit_and v_13619 (isBitSet v_13615 0)) (bit_and v_13618 (eq v_13628 (expression.bv_nat 1 1))));
      setRegister zf (bit_or (bit_and v_13619 (eq v_13616 (expression.bv_nat 8 0))) (bit_and v_13618 (eq v_13622 (expression.bv_nat 1 1))));
      pure ()
    pat_end;
    pattern fun (v_3069 : Mem) => do
      v_14570 <- evaluateAddress v_3069;
      v_14571 <- load v_14570 1;
      v_14573 <- eval (ashr (concat v_14571 (expression.bv_nat 1 0)) (expression.bv_nat 9 1));
      v_14574 <- eval (extract v_14573 0 8);
      store v_14570 v_14574 1;
      setRegister af undef;
      setRegister cf (isBitSet v_14573 8);
      setRegister of bit_zero;
      setRegister pf (parityFlag v_14574);
      setRegister sf (isBitSet v_14573 0);
      setRegister zf (zeroFlag v_14574);
      pure ()
    pat_end

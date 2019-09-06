def shrl1 : instruction :=
  definst "shrl" $ do
    pattern fun (_ : clReg) (v_3006 : reg (bv 32)) => do
      v_5063 <- getRegister rcx;
      v_5065 <- eval (bv_and (extract v_5063 56 64) (expression.bv_nat 8 31));
      v_5066 <- eval (eq v_5065 (expression.bv_nat 8 0));
      v_5067 <- getRegister zf;
      v_5068 <- getRegister v_3006;
      v_5071 <- eval (lshr (concat v_5068 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_5065));
      v_5072 <- eval (extract v_5071 0 32);
      v_5075 <- getRegister sf;
      v_5078 <- getRegister pf;
      v_5084 <- getRegister of;
      v_5088 <- getRegister cf;
      v_5092 <- getRegister af;
      setRegister (lhs.of_reg v_3006) v_5072;
      setRegister af (mux v_5066 v_5092 undef);
      setRegister cf (mux (uge v_5065 (expression.bv_nat 8 32)) undef (mux v_5066 v_5088 (isBitSet v_5071 32)));
      setRegister of (mux (eq v_5065 (expression.bv_nat 8 1)) (isBitSet v_5068 0) (mux v_5066 v_5084 undef));
      setRegister pf (mux v_5066 v_5078 (parityFlag (extract v_5071 24 32)));
      setRegister sf (mux v_5066 v_5075 (isBitSet v_5071 0));
      setRegister zf (mux v_5066 v_5067 (eq v_5072 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3010 : imm int) (v_3011 : reg (bv 32)) => do
      v_5102 <- eval (bv_and (handleImmediateWithSignExtend v_3010 8 8) (expression.bv_nat 8 31));
      v_5103 <- eval (eq v_5102 (expression.bv_nat 8 0));
      v_5104 <- getRegister zf;
      v_5105 <- getRegister v_3011;
      v_5108 <- eval (lshr (concat v_5105 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_5102));
      v_5109 <- eval (extract v_5108 0 32);
      v_5112 <- getRegister sf;
      v_5115 <- getRegister pf;
      v_5121 <- getRegister of;
      v_5125 <- getRegister cf;
      v_5129 <- getRegister af;
      setRegister (lhs.of_reg v_3011) v_5109;
      setRegister af (mux v_5103 v_5129 undef);
      setRegister cf (mux (uge v_5102 (expression.bv_nat 8 32)) undef (mux v_5103 v_5125 (isBitSet v_5108 32)));
      setRegister of (mux (eq v_5102 (expression.bv_nat 8 1)) (isBitSet v_5105 0) (mux v_5103 v_5121 undef));
      setRegister pf (mux v_5103 v_5115 (parityFlag (extract v_5108 24 32)));
      setRegister sf (mux v_5103 v_5112 (isBitSet v_5108 0));
      setRegister zf (mux v_5103 v_5104 (eq v_5109 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3015 : reg (bv 32)) => do
      v_6534 <- getRegister v_3015;
      v_6536 <- eval (lshr (concat v_6534 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      v_6537 <- eval (extract v_6536 0 32);
      setRegister (lhs.of_reg v_3015) v_6537;
      setRegister af undef;
      setRegister cf (isBitSet v_6536 32);
      setRegister of (isBitSet v_6534 0);
      setRegister pf (parityFlag (extract v_6536 24 32));
      setRegister sf (isBitSet v_6536 0);
      setRegister zf (zeroFlag v_6537);
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2993 : Mem) => do
      v_9424 <- evaluateAddress v_2993;
      v_9425 <- load v_9424 4;
      v_9427 <- getRegister rcx;
      v_9429 <- eval (bv_and (extract v_9427 56 64) (expression.bv_nat 8 31));
      v_9431 <- eval (lshr (concat v_9425 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_9429));
      v_9432 <- eval (extract v_9431 0 32);
      store v_9424 v_9432 4;
      v_9434 <- eval (eq v_9429 (expression.bv_nat 8 0));
      v_9435 <- getRegister zf;
      v_9438 <- getRegister sf;
      v_9441 <- getRegister pf;
      v_9447 <- getRegister of;
      v_9451 <- getRegister cf;
      v_9455 <- getRegister af;
      setRegister af (mux v_9434 v_9455 undef);
      setRegister cf (mux (uge v_9429 (expression.bv_nat 8 32)) undef (mux v_9434 v_9451 (isBitSet v_9431 32)));
      setRegister of (mux (eq v_9429 (expression.bv_nat 8 1)) (isBitSet v_9425 0) (mux v_9434 v_9447 undef));
      setRegister pf (mux v_9434 v_9441 (parityFlag (extract v_9431 24 32)));
      setRegister sf (mux v_9434 v_9438 (isBitSet v_9431 0));
      setRegister zf (mux v_9434 v_9435 (eq v_9432 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2997 : imm int) (v_2996 : Mem) => do
      v_9463 <- evaluateAddress v_2996;
      v_9464 <- load v_9463 4;
      v_9467 <- eval (bv_and (handleImmediateWithSignExtend v_2997 8 8) (expression.bv_nat 8 31));
      v_9469 <- eval (lshr (concat v_9464 (expression.bv_nat 1 0)) (concat (expression.bv_nat 25 0) v_9467));
      v_9470 <- eval (extract v_9469 0 32);
      store v_9463 v_9470 4;
      v_9472 <- eval (eq v_9467 (expression.bv_nat 8 0));
      v_9473 <- getRegister zf;
      v_9476 <- getRegister sf;
      v_9479 <- getRegister pf;
      v_9485 <- getRegister of;
      v_9489 <- getRegister cf;
      v_9493 <- getRegister af;
      setRegister af (mux v_9472 v_9493 undef);
      setRegister cf (mux (uge v_9467 (expression.bv_nat 8 32)) undef (mux v_9472 v_9489 (isBitSet v_9469 32)));
      setRegister of (mux (eq v_9467 (expression.bv_nat 8 1)) (isBitSet v_9464 0) (mux v_9472 v_9485 undef));
      setRegister pf (mux v_9472 v_9479 (parityFlag (extract v_9469 24 32)));
      setRegister sf (mux v_9472 v_9476 (isBitSet v_9469 0));
      setRegister zf (mux v_9472 v_9473 (eq v_9470 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_3000 : Mem) => do
      v_10105 <- evaluateAddress v_3000;
      v_10106 <- load v_10105 4;
      v_10108 <- eval (lshr (concat v_10106 (expression.bv_nat 1 0)) (expression.bv_nat 33 1));
      v_10109 <- eval (extract v_10108 0 32);
      store v_10105 v_10109 4;
      setRegister af undef;
      setRegister cf (isBitSet v_10108 32);
      setRegister of (isBitSet v_10106 0);
      setRegister pf (parityFlag (extract v_10108 24 32));
      setRegister sf (isBitSet v_10108 0);
      setRegister zf (zeroFlag v_10109);
      pure ()
    pat_end

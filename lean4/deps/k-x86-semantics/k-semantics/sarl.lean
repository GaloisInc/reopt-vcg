def sarl1 : instruction :=
  definst "sarl" $ do
    pattern fun cl (v_3068 : reg (bv 32)) => do
      v_7478 <- getRegister rcx;
      v_7480 <- eval (bv_and (extract v_7478 56 64) (expression.bv_nat 8 31));
      v_7481 <- eval (eq v_7480 (expression.bv_nat 8 0));
      v_7482 <- eval (notBool_ v_7481);
      v_7483 <- getRegister v_3068;
      v_7489 <- eval (ashr (mi 33 (svalueMInt (concat v_7483 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 25 0) v_7480)));
      v_7493 <- getRegister cf;
      v_7501 <- getRegister sf;
      v_7506 <- eval (extract v_7489 0 32);
      v_7509 <- getRegister zf;
      v_7514 <- eval (bit_and v_7482 undef);
      v_7515 <- getRegister af;
      v_7550 <- getRegister pf;
      v_7557 <- getRegister of;
      setRegister (lhs.of_reg v_3068) v_7506;
      setRegister of (mux (bit_and (notBool_ (eq v_7480 (expression.bv_nat 8 1))) (bit_or v_7514 (bit_and v_7481 (eq v_7557 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7482 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7489 31 32) (expression.bv_nat 1 1)) (eq (extract v_7489 30 31) (expression.bv_nat 1 1)))) (eq (extract v_7489 29 30) (expression.bv_nat 1 1)))) (eq (extract v_7489 28 29) (expression.bv_nat 1 1)))) (eq (extract v_7489 27 28) (expression.bv_nat 1 1)))) (eq (extract v_7489 26 27) (expression.bv_nat 1 1)))) (eq (extract v_7489 25 26) (expression.bv_nat 1 1)))) (eq (extract v_7489 24 25) (expression.bv_nat 1 1)))) (bit_and v_7481 (eq v_7550 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7514 (bit_and v_7481 (eq v_7515 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7482 (eq v_7506 (expression.bv_nat 32 0))) (bit_and v_7481 (eq v_7509 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7482 (eq (extract v_7489 0 1) (expression.bv_nat 1 1))) (bit_and v_7481 (eq v_7501 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7482 (eq (extract v_7489 32 33) (expression.bv_nat 1 1))) (bit_and v_7481 (eq v_7493 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3071 : imm int) (v_3073 : reg (bv 32)) => do
      v_7571 <- eval (bv_and (handleImmediateWithSignExtend v_3071 8 8) (expression.bv_nat 8 31));
      v_7572 <- eval (eq v_7571 (expression.bv_nat 8 0));
      v_7573 <- eval (notBool_ v_7572);
      v_7574 <- getRegister v_3073;
      v_7580 <- eval (ashr (mi 33 (svalueMInt (concat v_7574 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 25 0) v_7571)));
      v_7584 <- getRegister cf;
      v_7592 <- getRegister sf;
      v_7597 <- eval (extract v_7580 0 32);
      v_7600 <- getRegister zf;
      v_7605 <- eval (bit_and v_7573 undef);
      v_7606 <- getRegister af;
      v_7641 <- getRegister pf;
      v_7648 <- getRegister of;
      setRegister (lhs.of_reg v_3073) v_7597;
      setRegister of (mux (bit_and (notBool_ (eq v_7571 (expression.bv_nat 8 1))) (bit_or v_7605 (bit_and v_7572 (eq v_7648 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_7573 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7580 31 32) (expression.bv_nat 1 1)) (eq (extract v_7580 30 31) (expression.bv_nat 1 1)))) (eq (extract v_7580 29 30) (expression.bv_nat 1 1)))) (eq (extract v_7580 28 29) (expression.bv_nat 1 1)))) (eq (extract v_7580 27 28) (expression.bv_nat 1 1)))) (eq (extract v_7580 26 27) (expression.bv_nat 1 1)))) (eq (extract v_7580 25 26) (expression.bv_nat 1 1)))) (eq (extract v_7580 24 25) (expression.bv_nat 1 1)))) (bit_and v_7572 (eq v_7641 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_7605 (bit_and v_7572 (eq v_7606 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_7573 (eq v_7597 (expression.bv_nat 32 0))) (bit_and v_7572 (eq v_7600 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_7573 (eq (extract v_7580 0 1) (expression.bv_nat 1 1))) (bit_and v_7572 (eq v_7592 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_7573 (eq (extract v_7580 32 33) (expression.bv_nat 1 1))) (bit_and v_7572 (eq v_7584 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_3080 : reg (bv 32)) => do
      v_7663 <- getRegister v_3080;
      v_7667 <- eval (ashr (mi 33 (svalueMInt (concat v_7663 (expression.bv_nat 1 0)))) 1);
      v_7670 <- eval (extract v_7667 0 32);
      setRegister (lhs.of_reg v_3080) v_7670;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_7667 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_7670);
      setRegister sf (extract v_7667 0 1);
      setRegister cf (extract v_7667 32 33);
      pure ()
    pat_end;
    pattern fun (v_3076 : reg (bv 32)) => do
      v_9759 <- getRegister v_3076;
      v_9763 <- eval (ashr (mi 33 (svalueMInt (concat v_9759 (expression.bv_nat 1 0)))) 1);
      v_9770 <- eval (extract v_9763 0 32);
      setRegister (lhs.of_reg v_3076) v_9770;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9763 24 32));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_9770);
      setRegister sf (mux (eq (extract v_9763 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_9763 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3076 : reg (bv 32)) => do
      v_9781 <- getRegister v_3076;
      v_9785 <- eval (ashr (mi 33 (svalueMInt (concat v_9781 (expression.bv_nat 1 0)))) 1);
      v_9788 <- eval (extract v_9785 0 32);
      setRegister (lhs.of_reg v_3076) v_9788;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9785 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_9788);
      setRegister sf (extract v_9785 0 1);
      setRegister cf (extract v_9785 32 33);
      pure ()
    pat_end;
    pattern fun cl (v_3054 : Mem) => do
      v_16678 <- evaluateAddress v_3054;
      v_16679 <- load v_16678 4;
      v_16683 <- getRegister rcx;
      v_16685 <- eval (bv_and (extract v_16683 56 64) (expression.bv_nat 8 31));
      v_16688 <- eval (ashr (mi 33 (svalueMInt (concat v_16679 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 25 0) v_16685)));
      v_16689 <- eval (extract v_16688 0 32);
      store v_16678 v_16689 4;
      v_16691 <- eval (eq v_16685 (expression.bv_nat 8 0));
      v_16692 <- eval (notBool_ v_16691);
      v_16696 <- getRegister cf;
      v_16704 <- getRegister sf;
      v_16711 <- getRegister zf;
      v_16716 <- eval (bit_and v_16692 undef);
      v_16717 <- getRegister af;
      v_16752 <- getRegister pf;
      v_16759 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16685 (expression.bv_nat 8 1))) (bit_or v_16716 (bit_and v_16691 (eq v_16759 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16692 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16688 31 32) (expression.bv_nat 1 1)) (eq (extract v_16688 30 31) (expression.bv_nat 1 1)))) (eq (extract v_16688 29 30) (expression.bv_nat 1 1)))) (eq (extract v_16688 28 29) (expression.bv_nat 1 1)))) (eq (extract v_16688 27 28) (expression.bv_nat 1 1)))) (eq (extract v_16688 26 27) (expression.bv_nat 1 1)))) (eq (extract v_16688 25 26) (expression.bv_nat 1 1)))) (eq (extract v_16688 24 25) (expression.bv_nat 1 1)))) (bit_and v_16691 (eq v_16752 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16716 (bit_and v_16691 (eq v_16717 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16692 (eq v_16689 (expression.bv_nat 32 0))) (bit_and v_16691 (eq v_16711 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16692 (eq (extract v_16688 0 1) (expression.bv_nat 1 1))) (bit_and v_16691 (eq v_16704 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_16692 (eq (extract v_16688 32 33) (expression.bv_nat 1 1))) (bit_and v_16691 (eq v_16696 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3058 : imm int) (v_3057 : Mem) => do
      v_16771 <- evaluateAddress v_3057;
      v_16772 <- load v_16771 4;
      v_16777 <- eval (bv_and (handleImmediateWithSignExtend v_3058 8 8) (expression.bv_nat 8 31));
      v_16780 <- eval (ashr (mi 33 (svalueMInt (concat v_16772 (expression.bv_nat 1 0)))) (uvalueMInt (concat (expression.bv_nat 25 0) v_16777)));
      v_16781 <- eval (extract v_16780 0 32);
      store v_16771 v_16781 4;
      v_16783 <- eval (eq v_16777 (expression.bv_nat 8 0));
      v_16784 <- eval (notBool_ v_16783);
      v_16788 <- getRegister cf;
      v_16796 <- getRegister sf;
      v_16803 <- getRegister zf;
      v_16808 <- eval (bit_and v_16784 undef);
      v_16809 <- getRegister af;
      v_16844 <- getRegister pf;
      v_16851 <- getRegister of;
      setRegister of (mux (bit_and (notBool_ (eq v_16777 (expression.bv_nat 8 1))) (bit_or v_16808 (bit_and v_16783 (eq v_16851 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (bit_or (bit_and v_16784 (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_16780 31 32) (expression.bv_nat 1 1)) (eq (extract v_16780 30 31) (expression.bv_nat 1 1)))) (eq (extract v_16780 29 30) (expression.bv_nat 1 1)))) (eq (extract v_16780 28 29) (expression.bv_nat 1 1)))) (eq (extract v_16780 27 28) (expression.bv_nat 1 1)))) (eq (extract v_16780 26 27) (expression.bv_nat 1 1)))) (eq (extract v_16780 25 26) (expression.bv_nat 1 1)))) (eq (extract v_16780 24 25) (expression.bv_nat 1 1)))) (bit_and v_16783 (eq v_16844 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (mux (bit_or v_16808 (bit_and v_16783 (eq v_16809 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (bit_or (bit_and v_16784 (eq v_16781 (expression.bv_nat 32 0))) (bit_and v_16783 (eq v_16803 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (mux (bit_or (bit_and v_16784 (eq (extract v_16780 0 1) (expression.bv_nat 1 1))) (bit_and v_16783 (eq v_16796 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_16784 (eq (extract v_16780 32 33) (expression.bv_nat 1 1))) (bit_and v_16783 (eq v_16788 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3061 : Mem) => do
      v_18151 <- evaluateAddress v_3061;
      v_18152 <- load v_18151 4;
      v_18156 <- eval (ashr (mi 33 (svalueMInt (concat v_18152 (expression.bv_nat 1 0)))) 1);
      v_18157 <- eval (extract v_18156 0 32);
      store v_18151 v_18157 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18156 24 32));
      setRegister af (mux undef (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_18157);
      setRegister sf (mux (eq (extract v_18156 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (eq (extract v_18156 32 33) (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3061 : Mem) => do
      v_18174 <- evaluateAddress v_3061;
      v_18175 <- load v_18174 4;
      v_18179 <- eval (ashr (mi 33 (svalueMInt (concat v_18175 (expression.bv_nat 1 0)))) 1);
      v_18180 <- eval (extract v_18179 0 32);
      store v_18174 v_18180 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_18179 24 32));
      setRegister af undef;
      setRegister zf (zeroFlag v_18180);
      setRegister sf (extract v_18179 0 1);
      setRegister cf (extract v_18179 32 33);
      pure ()
    pat_end

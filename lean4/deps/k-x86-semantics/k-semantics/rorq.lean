def rorq1 : instruction :=
  definst "rorq" $ do
    pattern fun cl (v_2727 : reg (bv 64)) => do
      v_5520 <- getRegister rcx;
      v_5522 <- eval (bv_and (extract v_5520 56 64) (expression.bv_nat 8 63));
      v_5523 <- eval (eq v_5522 (expression.bv_nat 8 0));
      v_5524 <- eval (notBool_ v_5523);
      v_5525 <- getRegister v_2727;
      v_5528 <- eval (rorHelper v_5525 (uvalueMInt (concat (expression.bv_nat 56 0) v_5522)) 0);
      v_5530 <- eval (eq (extract v_5528 0 1) (expression.bv_nat 1 1));
      v_5532 <- getRegister cf;
      v_5537 <- eval (eq v_5522 (expression.bv_nat 8 1));
      v_5545 <- getRegister of;
      setRegister (lhs.of_reg v_2727) v_5528;
      setRegister of (mux (bit_or (bit_and v_5537 (notBool_ (eq v_5530 (eq (extract v_5528 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5537) (bit_or (bit_and v_5524 undef) (bit_and v_5523 (eq v_5545 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5524 v_5530) (bit_and v_5523 (eq v_5532 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2728 : imm int) (v_2732 : reg (bv 64)) => do
      v_5556 <- eval (bv_and (handleImmediateWithSignExtend v_2728 8 8) (expression.bv_nat 8 63));
      v_5557 <- eval (eq v_5556 (expression.bv_nat 8 0));
      v_5558 <- eval (notBool_ v_5557);
      v_5559 <- getRegister v_2732;
      v_5562 <- eval (rorHelper v_5559 (uvalueMInt (concat (expression.bv_nat 56 0) v_5556)) 0);
      v_5564 <- eval (eq (extract v_5562 0 1) (expression.bv_nat 1 1));
      v_5566 <- getRegister cf;
      v_5571 <- eval (eq v_5556 (expression.bv_nat 8 1));
      v_5579 <- getRegister of;
      setRegister (lhs.of_reg v_2732) v_5562;
      setRegister of (mux (bit_or (bit_and v_5571 (notBool_ (eq v_5564 (eq (extract v_5562 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5571) (bit_or (bit_and v_5558 undef) (bit_and v_5557 (eq v_5579 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5558 v_5564) (bit_and v_5557 (eq v_5566 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2736 : reg (bv 64)) => do
      v_5589 <- getRegister v_2736;
      v_5591 <- eval (bitwidthMInt v_5589);
      v_5592 <- eval (sub v_5591 1);
      v_5596 <- eval (add (lshr v_5589 1) (concat (extract v_5589 v_5592 v_5591) (mi v_5592 0)));
      v_5597 <- eval (extract v_5596 0 1);
      setRegister (lhs.of_reg v_2736) v_5596;
      setRegister of (mux (notBool_ (eq (eq v_5597 (expression.bv_nat 1 1)) (eq (extract v_5596 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5597;
      pure ()
    pat_end;
    pattern fun cl (v_2714 : Mem) => do
      v_15085 <- evaluateAddress v_2714;
      v_15086 <- load v_15085 8;
      v_15087 <- getRegister rcx;
      v_15089 <- eval (bv_and (extract v_15087 56 64) (expression.bv_nat 8 63));
      v_15092 <- eval (rorHelper v_15086 (uvalueMInt (concat (expression.bv_nat 56 0) v_15089)) 0);
      store v_15085 v_15092 8;
      v_15094 <- eval (eq v_15089 (expression.bv_nat 8 0));
      v_15095 <- eval (notBool_ v_15094);
      v_15097 <- eval (eq (extract v_15092 0 1) (expression.bv_nat 1 1));
      v_15099 <- getRegister cf;
      v_15104 <- eval (eq v_15089 (expression.bv_nat 8 1));
      v_15112 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15104 (notBool_ (eq v_15097 (eq (extract v_15092 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15104) (bit_or (bit_and v_15095 undef) (bit_and v_15094 (eq v_15112 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_15095 v_15097) (bit_and v_15094 (eq v_15099 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2717 : imm int) (v_2718 : Mem) => do
      v_15121 <- evaluateAddress v_2718;
      v_15122 <- load v_15121 8;
      v_15124 <- eval (bv_and (handleImmediateWithSignExtend v_2717 8 8) (expression.bv_nat 8 63));
      v_15127 <- eval (rorHelper v_15122 (uvalueMInt (concat (expression.bv_nat 56 0) v_15124)) 0);
      store v_15121 v_15127 8;
      v_15129 <- eval (eq v_15124 (expression.bv_nat 8 0));
      v_15130 <- eval (notBool_ v_15129);
      v_15132 <- eval (eq (extract v_15127 0 1) (expression.bv_nat 1 1));
      v_15134 <- getRegister cf;
      v_15139 <- eval (eq v_15124 (expression.bv_nat 8 1));
      v_15147 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_15139 (notBool_ (eq v_15132 (eq (extract v_15127 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_15139) (bit_or (bit_and v_15130 undef) (bit_and v_15129 (eq v_15147 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_15130 v_15132) (bit_and v_15129 (eq v_15134 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

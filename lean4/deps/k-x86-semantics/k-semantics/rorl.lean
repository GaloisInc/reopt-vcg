def rorl1 : instruction :=
  definst "rorl" $ do
    pattern fun cl (v_2715 : reg (bv 32)) => do
      v_5452 <- getRegister rcx;
      v_5454 <- eval (bv_and (extract v_5452 56 64) (expression.bv_nat 8 31));
      v_5455 <- eval (eq v_5454 (expression.bv_nat 8 0));
      v_5456 <- eval (notBool_ v_5455);
      v_5457 <- getRegister v_2715;
      v_5460 <- eval (rorHelper v_5457 (uvalueMInt (concat (expression.bv_nat 24 0) v_5454)) 0);
      v_5462 <- eval (eq (extract v_5460 0 1) (expression.bv_nat 1 1));
      v_5464 <- getRegister cf;
      v_5469 <- eval (eq v_5454 (expression.bv_nat 8 1));
      v_5477 <- getRegister of;
      setRegister (lhs.of_reg v_2715) v_5460;
      setRegister of (mux (bit_or (bit_and v_5469 (notBool_ (eq v_5462 (eq (extract v_5460 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5469) (bit_or (bit_and v_5456 undef) (bit_and v_5455 (eq v_5477 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5456 v_5462) (bit_and v_5455 (eq v_5464 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2718 : imm int) (v_2720 : reg (bv 32)) => do
      v_5488 <- eval (bv_and (handleImmediateWithSignExtend v_2718 8 8) (expression.bv_nat 8 31));
      v_5489 <- eval (eq v_5488 (expression.bv_nat 8 0));
      v_5490 <- eval (notBool_ v_5489);
      v_5491 <- getRegister v_2720;
      v_5494 <- eval (rorHelper v_5491 (uvalueMInt (concat (expression.bv_nat 24 0) v_5488)) 0);
      v_5496 <- eval (eq (extract v_5494 0 1) (expression.bv_nat 1 1));
      v_5498 <- getRegister cf;
      v_5503 <- eval (eq v_5488 (expression.bv_nat 8 1));
      v_5511 <- getRegister of;
      setRegister (lhs.of_reg v_2720) v_5494;
      setRegister of (mux (bit_or (bit_and v_5503 (notBool_ (eq v_5496 (eq (extract v_5494 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5503) (bit_or (bit_and v_5490 undef) (bit_and v_5489 (eq v_5511 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5490 v_5496) (bit_and v_5489 (eq v_5498 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2724 : reg (bv 32)) => do
      v_5521 <- getRegister v_2724;
      v_5525 <- eval (add (lshr v_5521 1) (concat (extract v_5521 31 32) (expression.bv_nat 31 0)));
      v_5526 <- eval (extract v_5525 0 1);
      setRegister (lhs.of_reg v_2724) v_5525;
      setRegister of (mux (notBool_ (eq (eq v_5526 (expression.bv_nat 1 1)) (eq (extract v_5525 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5526;
      pure ()
    pat_end;
    pattern fun cl (v_2704 : Mem) => do
      v_14790 <- evaluateAddress v_2704;
      v_14791 <- load v_14790 4;
      v_14792 <- getRegister rcx;
      v_14794 <- eval (bv_and (extract v_14792 56 64) (expression.bv_nat 8 31));
      v_14797 <- eval (rorHelper v_14791 (uvalueMInt (concat (expression.bv_nat 24 0) v_14794)) 0);
      store v_14790 v_14797 4;
      v_14799 <- eval (eq v_14794 (expression.bv_nat 8 0));
      v_14800 <- eval (notBool_ v_14799);
      v_14802 <- eval (eq (extract v_14797 0 1) (expression.bv_nat 1 1));
      v_14804 <- getRegister cf;
      v_14809 <- eval (eq v_14794 (expression.bv_nat 8 1));
      v_14817 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14809 (notBool_ (eq v_14802 (eq (extract v_14797 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14809) (bit_or (bit_and v_14800 undef) (bit_and v_14799 (eq v_14817 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14800 v_14802) (bit_and v_14799 (eq v_14804 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2708 : imm int) (v_2707 : Mem) => do
      v_14826 <- evaluateAddress v_2707;
      v_14827 <- load v_14826 4;
      v_14829 <- eval (bv_and (handleImmediateWithSignExtend v_2708 8 8) (expression.bv_nat 8 31));
      v_14832 <- eval (rorHelper v_14827 (uvalueMInt (concat (expression.bv_nat 24 0) v_14829)) 0);
      store v_14826 v_14832 4;
      v_14834 <- eval (eq v_14829 (expression.bv_nat 8 0));
      v_14835 <- eval (notBool_ v_14834);
      v_14837 <- eval (eq (extract v_14832 0 1) (expression.bv_nat 1 1));
      v_14839 <- getRegister cf;
      v_14844 <- eval (eq v_14829 (expression.bv_nat 8 1));
      v_14852 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14844 (notBool_ (eq v_14837 (eq (extract v_14832 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14844) (bit_or (bit_and v_14835 undef) (bit_and v_14834 (eq v_14852 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14835 v_14837) (bit_and v_14834 (eq v_14839 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

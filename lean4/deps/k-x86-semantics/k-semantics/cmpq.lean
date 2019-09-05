def cmpq1 : instruction :=
  definst "cmpq" $ do
    pattern fun (v_2454 : imm int) (v_2452 : reg (bv 64)) => do
      v_3804 <- eval (handleImmediateWithSignExtend v_2454 32 32);
      v_3805 <- eval (sext v_3804 64);
      v_3809 <- getRegister v_2452;
      v_3811 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3805 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3809));
      v_3814 <- eval (isBitSet v_3811 1);
      v_3819 <- eval (eq (bv_xor (extract v_3805 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_3804 27) (isBitSet v_3809 59))) (isBitSet v_3811 60)));
      setRegister cf (notBool_ (isBitSet v_3811 0));
      setRegister of (bit_and (eq v_3819 (isBitSet v_3809 0)) (notBool_ (eq v_3819 v_3814)));
      setRegister pf (parityFlag (extract v_3811 57 65));
      setRegister sf v_3814;
      setRegister zf (zeroFlag (extract v_3811 1 65));
      pure ()
    pat_end;
    pattern fun (v_2461 : reg (bv 64)) (v_2462 : reg (bv 64)) => do
      v_3844 <- getRegister v_2461;
      v_3848 <- getRegister v_2462;
      v_3850 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3844 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3848));
      v_3853 <- eval (isBitSet v_3850 1);
      v_3858 <- eval (eq (bv_xor (extract v_3844 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3844 v_3848) 59) (isBitSet v_3850 60)));
      setRegister cf (notBool_ (isBitSet v_3850 0));
      setRegister of (bit_and (eq v_3858 (isBitSet v_3848 0)) (notBool_ (eq v_3858 v_3853)));
      setRegister pf (parityFlag (extract v_3850 57 65));
      setRegister sf v_3853;
      setRegister zf (zeroFlag (extract v_3850 1 65));
      pure ()
    pat_end;
    pattern fun (v_2445 : imm int) (v_2444 : Mem) => do
      v_7556 <- eval (handleImmediateWithSignExtend v_2445 32 32);
      v_7557 <- eval (sext v_7556 64);
      v_7561 <- evaluateAddress v_2444;
      v_7562 <- load v_7561 8;
      v_7564 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7557 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7562));
      v_7567 <- eval (isBitSet v_7564 1);
      v_7572 <- eval (eq (bv_xor (extract v_7557 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_7556 27) (isBitSet v_7562 59))) (isBitSet v_7564 60)));
      setRegister cf (notBool_ (isBitSet v_7564 0));
      setRegister of (bit_and (eq v_7572 (isBitSet v_7562 0)) (notBool_ (eq v_7572 v_7567)));
      setRegister pf (parityFlag (extract v_7564 57 65));
      setRegister sf v_7567;
      setRegister zf (zeroFlag (extract v_7564 1 65));
      pure ()
    pat_end;
    pattern fun (v_2449 : reg (bv 64)) (v_2448 : Mem) => do
      v_7593 <- getRegister v_2449;
      v_7597 <- evaluateAddress v_2448;
      v_7598 <- load v_7597 8;
      v_7600 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7593 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7598));
      v_7603 <- eval (isBitSet v_7600 1);
      v_7608 <- eval (eq (bv_xor (extract v_7593 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7593 v_7598) 59) (isBitSet v_7600 60)));
      setRegister cf (notBool_ (isBitSet v_7600 0));
      setRegister of (bit_and (eq v_7608 (isBitSet v_7598 0)) (notBool_ (eq v_7608 v_7603)));
      setRegister pf (parityFlag (extract v_7600 57 65));
      setRegister sf v_7603;
      setRegister zf (zeroFlag (extract v_7600 1 65));
      pure ()
    pat_end;
    pattern fun (v_2457 : Mem) (v_2458 : reg (bv 64)) => do
      v_7627 <- evaluateAddress v_2457;
      v_7628 <- load v_7627 8;
      v_7632 <- getRegister v_2458;
      v_7634 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7628 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7632));
      v_7637 <- eval (isBitSet v_7634 1);
      v_7642 <- eval (eq (bv_xor (extract v_7628 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7628 v_7632) 59) (isBitSet v_7634 60)));
      setRegister cf (notBool_ (isBitSet v_7634 0));
      setRegister of (bit_and (eq v_7642 (isBitSet v_7632 0)) (notBool_ (eq v_7642 v_7637)));
      setRegister pf (parityFlag (extract v_7634 57 65));
      setRegister sf v_7637;
      setRegister zf (zeroFlag (extract v_7634 1 65));
      pure ()
    pat_end

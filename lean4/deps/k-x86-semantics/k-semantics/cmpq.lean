def cmpq1 : instruction :=
  definst "cmpq" $ do
    pattern fun (v_2479 : imm int) (v_2480 : reg (bv 64)) => do
      v_3831 <- eval (handleImmediateWithSignExtend v_2479 32 32);
      v_3832 <- eval (sext v_3831 64);
      v_3836 <- getRegister v_2480;
      v_3838 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3832 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3836));
      v_3841 <- eval (isBitSet v_3838 1);
      v_3846 <- eval (eq (bv_xor (extract v_3832 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_3831 27) (isBitSet v_3836 59))) (isBitSet v_3838 60)));
      setRegister cf (isBitClear v_3838 0);
      setRegister of (bit_and (eq v_3846 (isBitSet v_3836 0)) (notBool_ (eq v_3846 v_3841)));
      setRegister pf (parityFlag (extract v_3838 57 65));
      setRegister sf v_3841;
      setRegister zf (zeroFlag (extract v_3838 1 65));
      pure ()
    pat_end;
    pattern fun (v_2488 : reg (bv 64)) (v_2489 : reg (bv 64)) => do
      v_3870 <- getRegister v_2488;
      v_3874 <- getRegister v_2489;
      v_3876 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3870 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3874));
      v_3879 <- eval (isBitSet v_3876 1);
      v_3884 <- eval (eq (bv_xor (extract v_3870 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3870 v_3874) 59) (isBitSet v_3876 60)));
      setRegister cf (isBitClear v_3876 0);
      setRegister of (bit_and (eq v_3884 (isBitSet v_3874 0)) (notBool_ (eq v_3884 v_3879)));
      setRegister pf (parityFlag (extract v_3876 57 65));
      setRegister sf v_3879;
      setRegister zf (zeroFlag (extract v_3876 1 65));
      pure ()
    pat_end;
    pattern fun (v_2472 : imm int) (v_2471 : Mem) => do
      v_7572 <- eval (handleImmediateWithSignExtend v_2472 32 32);
      v_7573 <- eval (sext v_7572 64);
      v_7577 <- evaluateAddress v_2471;
      v_7578 <- load v_7577 8;
      v_7580 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7573 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7578));
      v_7583 <- eval (isBitSet v_7580 1);
      v_7588 <- eval (eq (bv_xor (extract v_7573 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_7572 27) (isBitSet v_7578 59))) (isBitSet v_7580 60)));
      setRegister cf (isBitClear v_7580 0);
      setRegister of (bit_and (eq v_7588 (isBitSet v_7578 0)) (notBool_ (eq v_7588 v_7583)));
      setRegister pf (parityFlag (extract v_7580 57 65));
      setRegister sf v_7583;
      setRegister zf (zeroFlag (extract v_7580 1 65));
      pure ()
    pat_end;
    pattern fun (v_2476 : reg (bv 64)) (v_2475 : Mem) => do
      v_7608 <- getRegister v_2476;
      v_7612 <- evaluateAddress v_2475;
      v_7613 <- load v_7612 8;
      v_7615 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7608 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7613));
      v_7618 <- eval (isBitSet v_7615 1);
      v_7623 <- eval (eq (bv_xor (extract v_7608 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7608 v_7613) 59) (isBitSet v_7615 60)));
      setRegister cf (isBitClear v_7615 0);
      setRegister of (bit_and (eq v_7623 (isBitSet v_7613 0)) (notBool_ (eq v_7623 v_7618)));
      setRegister pf (parityFlag (extract v_7615 57 65));
      setRegister sf v_7618;
      setRegister zf (zeroFlag (extract v_7615 1 65));
      pure ()
    pat_end;
    pattern fun (v_2484 : Mem) (v_2485 : reg (bv 64)) => do
      v_7641 <- evaluateAddress v_2484;
      v_7642 <- load v_7641 8;
      v_7646 <- getRegister v_2485;
      v_7648 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7642 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7646));
      v_7651 <- eval (isBitSet v_7648 1);
      v_7656 <- eval (eq (bv_xor (extract v_7642 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_7642 v_7646) 59) (isBitSet v_7648 60)));
      setRegister cf (isBitClear v_7648 0);
      setRegister of (bit_and (eq v_7656 (isBitSet v_7646 0)) (notBool_ (eq v_7656 v_7651)));
      setRegister pf (parityFlag (extract v_7648 57 65));
      setRegister sf v_7651;
      setRegister zf (zeroFlag (extract v_7648 1 65));
      pure ()
    pat_end

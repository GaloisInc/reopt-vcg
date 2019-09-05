def cmpl1 : instruction :=
  definst "cmpl" $ do
    pattern fun (v_3429 : imm int) (v_3433 : reg (bv 32)) => do
      v_5553 <- eval (handleImmediateWithSignExtend v_3429 32 32);
      v_5557 <- getRegister v_3433;
      v_5559 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5553 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5557));
      v_5562 <- eval (isBitSet v_5559 1);
      v_5567 <- eval (eq (bv_xor (extract v_5553 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5553 v_5557) 27) (isBitSet v_5559 28)));
      setRegister cf (notBool_ (isBitSet v_5559 0));
      setRegister of (bit_and (eq v_5567 (isBitSet v_5557 0)) (notBool_ (eq v_5567 v_5562)));
      setRegister pf (parityFlag (extract v_5559 25 33));
      setRegister sf v_5562;
      setRegister zf (zeroFlag (extract v_5559 1 33));
      pure ()
    pat_end;
    pattern fun (v_3441 : reg (bv 32)) (v_3442 : reg (bv 32)) => do
      v_5590 <- getRegister v_3441;
      v_5594 <- getRegister v_3442;
      v_5596 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5590 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5594));
      v_5599 <- eval (isBitSet v_5596 1);
      v_5604 <- eval (eq (bv_xor (extract v_5590 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5590 v_5594) 27) (isBitSet v_5596 28)));
      setRegister cf (notBool_ (isBitSet v_5596 0));
      setRegister of (bit_and (eq v_5604 (isBitSet v_5594 0)) (notBool_ (eq v_5604 v_5599)));
      setRegister pf (parityFlag (extract v_5596 25 33));
      setRegister sf v_5599;
      setRegister zf (zeroFlag (extract v_5596 1 33));
      pure ()
    pat_end;
    pattern fun (v_3421 : imm int) (v_3422 : Mem) => do
      v_8797 <- eval (handleImmediateWithSignExtend v_3421 32 32);
      v_8801 <- evaluateAddress v_3422;
      v_8802 <- load v_8801 4;
      v_8804 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8797 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8802));
      v_8807 <- eval (isBitSet v_8804 1);
      v_8812 <- eval (eq (bv_xor (extract v_8797 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8797 v_8802) 27) (isBitSet v_8804 28)));
      setRegister cf (notBool_ (isBitSet v_8804 0));
      setRegister of (bit_and (eq v_8812 (isBitSet v_8802 0)) (notBool_ (eq v_8812 v_8807)));
      setRegister pf (parityFlag (extract v_8804 25 33));
      setRegister sf v_8807;
      setRegister zf (zeroFlag (extract v_8804 1 33));
      pure ()
    pat_end;
    pattern fun (v_3428 : reg (bv 32)) (v_3425 : Mem) => do
      v_8831 <- getRegister v_3428;
      v_8835 <- evaluateAddress v_3425;
      v_8836 <- load v_8835 4;
      v_8838 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8831 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8836));
      v_8841 <- eval (isBitSet v_8838 1);
      v_8846 <- eval (eq (bv_xor (extract v_8831 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8831 v_8836) 27) (isBitSet v_8838 28)));
      setRegister cf (notBool_ (isBitSet v_8838 0));
      setRegister of (bit_and (eq v_8846 (isBitSet v_8836 0)) (notBool_ (eq v_8846 v_8841)));
      setRegister pf (parityFlag (extract v_8838 25 33));
      setRegister sf v_8841;
      setRegister zf (zeroFlag (extract v_8838 1 33));
      pure ()
    pat_end;
    pattern fun (v_3434 : Mem) (v_3437 : reg (bv 32)) => do
      v_8865 <- evaluateAddress v_3434;
      v_8866 <- load v_8865 4;
      v_8870 <- getRegister v_3437;
      v_8872 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8866 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8870));
      v_8875 <- eval (isBitSet v_8872 1);
      v_8880 <- eval (eq (bv_xor (extract v_8866 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8866 v_8870) 27) (isBitSet v_8872 28)));
      setRegister cf (notBool_ (isBitSet v_8872 0));
      setRegister of (bit_and (eq v_8880 (isBitSet v_8870 0)) (notBool_ (eq v_8880 v_8875)));
      setRegister pf (parityFlag (extract v_8872 25 33));
      setRegister sf v_8875;
      setRegister zf (zeroFlag (extract v_8872 1 33));
      pure ()
    pat_end

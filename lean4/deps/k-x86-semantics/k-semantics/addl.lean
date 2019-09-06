def addl1 : instruction :=
  definst "addl" $ do
    pattern fun (v_2669 : imm int) (v_2671 : reg (bv 32)) => do
      v_4591 <- eval (handleImmediateWithSignExtend v_2669 32 32);
      v_4593 <- getRegister v_2671;
      v_4595 <- eval (add (concat (expression.bv_nat 1 0) v_4591) (concat (expression.bv_nat 1 0) v_4593));
      v_4596 <- eval (extract v_4595 1 33);
      setRegister (lhs.of_reg v_2671) v_4596;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4591 v_4593) 27) (isBitSet v_4595 28)));
      setRegister cf (isBitSet v_4595 0);
      setRegister of (overflowFlag v_4591 v_4593 v_4596);
      setRegister pf (parityFlag (extract v_4595 25 33));
      setRegister sf (isBitSet v_4595 1);
      setRegister zf (zeroFlag v_4596);
      pure ()
    pat_end;
    pattern fun (v_2679 : reg (bv 32)) (v_2680 : reg (bv 32)) => do
      v_4619 <- getRegister v_2679;
      v_4621 <- getRegister v_2680;
      v_4623 <- eval (add (concat (expression.bv_nat 1 0) v_4619) (concat (expression.bv_nat 1 0) v_4621));
      v_4624 <- eval (extract v_4623 1 33);
      setRegister (lhs.of_reg v_2680) v_4624;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4619 v_4621) 27) (isBitSet v_4623 28)));
      setRegister cf (isBitSet v_4623 0);
      setRegister of (overflowFlag v_4619 v_4621 v_4624);
      setRegister pf (parityFlag (extract v_4623 25 33));
      setRegister sf (isBitSet v_4623 1);
      setRegister zf (zeroFlag v_4624);
      pure ()
    pat_end;
    pattern fun (v_2674 : Mem) (v_2675 : reg (bv 32)) => do
      v_8725 <- evaluateAddress v_2674;
      v_8726 <- load v_8725 4;
      v_8728 <- getRegister v_2675;
      v_8730 <- eval (add (concat (expression.bv_nat 1 0) v_8726) (concat (expression.bv_nat 1 0) v_8728));
      v_8731 <- eval (extract v_8730 1 33);
      setRegister (lhs.of_reg v_2675) v_8731;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8726 v_8728) 27) (isBitSet v_8730 28)));
      setRegister cf (isBitSet v_8730 0);
      setRegister of (overflowFlag v_8726 v_8728 v_8731);
      setRegister pf (parityFlag (extract v_8730 25 33));
      setRegister sf (isBitSet v_8730 1);
      setRegister zf (zeroFlag v_8731);
      pure ()
    pat_end;
    pattern fun (v_2662 : imm int) (v_2661 : Mem) => do
      v_10131 <- evaluateAddress v_2661;
      v_10132 <- eval (handleImmediateWithSignExtend v_2662 32 32);
      v_10134 <- load v_10131 4;
      v_10136 <- eval (add (concat (expression.bv_nat 1 0) v_10132) (concat (expression.bv_nat 1 0) v_10134));
      v_10137 <- eval (extract v_10136 1 33);
      store v_10131 v_10137 4;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10132 v_10134) 27) (isBitSet v_10136 28)));
      setRegister cf (isBitSet v_10136 0);
      setRegister of (overflowFlag v_10132 v_10134 v_10137);
      setRegister pf (parityFlag (extract v_10136 25 33));
      setRegister sf (isBitSet v_10136 1);
      setRegister zf (zeroFlag v_10137);
      pure ()
    pat_end;
    pattern fun (v_2666 : reg (bv 32)) (v_2665 : Mem) => do
      v_10156 <- evaluateAddress v_2665;
      v_10157 <- getRegister v_2666;
      v_10159 <- load v_10156 4;
      v_10161 <- eval (add (concat (expression.bv_nat 1 0) v_10157) (concat (expression.bv_nat 1 0) v_10159));
      v_10162 <- eval (extract v_10161 1 33);
      store v_10156 v_10162 4;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_10157 v_10159) 27) (isBitSet v_10161 28)));
      setRegister cf (isBitSet v_10161 0);
      setRegister of (overflowFlag v_10157 v_10159 v_10162);
      setRegister pf (parityFlag (extract v_10161 25 33));
      setRegister sf (isBitSet v_10161 1);
      setRegister zf (zeroFlag v_10162);
      pure ()
    pat_end

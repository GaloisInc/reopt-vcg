def subb1 : instruction :=
  definst "subb" $ do
    pattern fun (v_3221 : imm int) (v_3222 : reg (bv 8)) => do
      v_5671 <- eval (handleImmediateWithSignExtend v_3221 8 8);
      v_5675 <- getRegister v_3222;
      v_5677 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5671 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5675));
      v_5678 <- eval (extract v_5677 1 9);
      v_5680 <- eval (isBitSet v_5677 1);
      v_5684 <- eval (eq (bv_xor (extract v_5671 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3222) v_5678;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5671 v_5675) 3) (isBitSet v_5677 4)));
      setRegister cf (isBitClear v_5677 0);
      setRegister of (bit_and (eq v_5684 (isBitSet v_5675 0)) (notBool_ (eq v_5684 v_5680)));
      setRegister pf (parityFlag v_5678);
      setRegister sf v_5680;
      setRegister zf (zeroFlag v_5678);
      pure ()
    pat_end;
    pattern fun (v_3235 : reg (bv 8)) (v_3236 : reg (bv 8)) => do
      v_5739 <- getRegister v_3235;
      v_5743 <- getRegister v_3236;
      v_5745 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5739 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5743));
      v_5746 <- eval (extract v_5745 1 9);
      v_5748 <- eval (isBitSet v_5745 1);
      v_5752 <- eval (eq (bv_xor (extract v_5739 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3236) v_5746;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5739 v_5743) 3) (isBitSet v_5745 4)));
      setRegister cf (isBitClear v_5745 0);
      setRegister of (bit_and (eq v_5752 (isBitSet v_5743 0)) (notBool_ (eq v_5752 v_5748)));
      setRegister pf (parityFlag v_5746);
      setRegister sf v_5748;
      setRegister zf (zeroFlag v_5746);
      pure ()
    pat_end;
    pattern fun (v_3226 : Mem) (v_3227 : reg (bv 8)) => do
      v_8609 <- evaluateAddress v_3226;
      v_8610 <- load v_8609 1;
      v_8614 <- getRegister v_3227;
      v_8616 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8610 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8614));
      v_8617 <- eval (extract v_8616 1 9);
      v_8619 <- eval (isBitSet v_8616 1);
      v_8623 <- eval (eq (bv_xor (extract v_8610 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3227) v_8617;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8610 v_8614) 3) (isBitSet v_8616 4)));
      setRegister cf (isBitClear v_8616 0);
      setRegister of (bit_and (eq v_8623 (isBitSet v_8614 0)) (notBool_ (eq v_8623 v_8619)));
      setRegister pf (parityFlag v_8617);
      setRegister sf v_8619;
      setRegister zf (zeroFlag v_8617);
      pure ()
    pat_end;
    pattern fun (v_3191 : imm int) (v_3190 : Mem) => do
      v_9782 <- evaluateAddress v_3190;
      v_9783 <- eval (handleImmediateWithSignExtend v_3191 8 8);
      v_9787 <- load v_9782 1;
      v_9789 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9783 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_9787));
      v_9790 <- eval (extract v_9789 1 9);
      store v_9782 v_9790 1;
      v_9793 <- eval (isBitSet v_9789 1);
      v_9797 <- eval (eq (bv_xor (extract v_9783 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9783 v_9787) 3) (isBitSet v_9789 4)));
      setRegister cf (isBitClear v_9789 0);
      setRegister of (bit_and (eq v_9797 (isBitSet v_9787 0)) (notBool_ (eq v_9797 v_9793)));
      setRegister pf (parityFlag v_9790);
      setRegister sf v_9793;
      setRegister zf (zeroFlag v_9790);
      pure ()
    pat_end;
    pattern fun (v_3199 : reg (bv 8)) (v_3198 : Mem) => do
      v_9848 <- evaluateAddress v_3198;
      v_9849 <- getRegister v_3199;
      v_9853 <- load v_9848 1;
      v_9855 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9849 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_9853));
      v_9856 <- eval (extract v_9855 1 9);
      store v_9848 v_9856 1;
      v_9859 <- eval (isBitSet v_9855 1);
      v_9863 <- eval (eq (bv_xor (extract v_9849 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9849 v_9853) 3) (isBitSet v_9855 4)));
      setRegister cf (isBitClear v_9855 0);
      setRegister of (bit_and (eq v_9863 (isBitSet v_9853 0)) (notBool_ (eq v_9863 v_9859)));
      setRegister pf (parityFlag v_9856);
      setRegister sf v_9859;
      setRegister zf (zeroFlag v_9856);
      pure ()
    pat_end

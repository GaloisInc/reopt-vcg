def subl1 : instruction :=
  definst "subl" $ do
    pattern fun (v_3253 : imm int) (v_3252 : reg (bv 32)) => do
      v_5815 <- eval (handleImmediateWithSignExtend v_3253 32 32);
      v_5819 <- getRegister v_3252;
      v_5821 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5815 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5819));
      v_5822 <- eval (extract v_5821 1 33);
      v_5824 <- eval (isBitSet v_5821 1);
      v_5829 <- eval (eq (bv_xor (extract v_5815 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3252) v_5822;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5815 v_5819) 27) (isBitSet v_5821 28)));
      setRegister cf (isBitClear v_5821 0);
      setRegister of (bit_and (eq v_5829 (isBitSet v_5819 0)) (notBool_ (eq v_5829 v_5824)));
      setRegister pf (parityFlag (extract v_5821 25 33));
      setRegister sf v_5824;
      setRegister zf (zeroFlag v_5822);
      pure ()
    pat_end;
    pattern fun (v_3261 : reg (bv 32)) (v_3262 : reg (bv 32)) => do
      v_5852 <- getRegister v_3261;
      v_5856 <- getRegister v_3262;
      v_5858 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5852 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_5856));
      v_5859 <- eval (extract v_5858 1 33);
      v_5861 <- eval (isBitSet v_5858 1);
      v_5866 <- eval (eq (bv_xor (extract v_5852 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3262) v_5859;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_5852 v_5856) 27) (isBitSet v_5858 28)));
      setRegister cf (isBitClear v_5858 0);
      setRegister of (bit_and (eq v_5866 (isBitSet v_5856 0)) (notBool_ (eq v_5866 v_5861)));
      setRegister pf (parityFlag (extract v_5858 25 33));
      setRegister sf v_5861;
      setRegister zf (zeroFlag v_5859);
      pure ()
    pat_end;
    pattern fun (v_3257 : Mem) (v_3258 : reg (bv 32)) => do
      v_8644 <- evaluateAddress v_3257;
      v_8645 <- load v_8644 4;
      v_8649 <- getRegister v_3258;
      v_8651 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8645 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_8649));
      v_8652 <- eval (extract v_8651 1 33);
      v_8654 <- eval (isBitSet v_8651 1);
      v_8659 <- eval (eq (bv_xor (extract v_8645 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3258) v_8652;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8645 v_8649) 27) (isBitSet v_8651 28)));
      setRegister cf (isBitClear v_8651 0);
      setRegister of (bit_and (eq v_8659 (isBitSet v_8649 0)) (notBool_ (eq v_8659 v_8654)));
      setRegister pf (parityFlag (extract v_8651 25 33));
      setRegister sf v_8654;
      setRegister zf (zeroFlag v_8652);
      pure ()
    pat_end;
    pattern fun (v_3245 : imm int) (v_3244 : Mem) => do
      v_9881 <- evaluateAddress v_3244;
      v_9882 <- eval (handleImmediateWithSignExtend v_3245 32 32);
      v_9886 <- load v_9881 4;
      v_9888 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9882 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_9886));
      v_9889 <- eval (extract v_9888 1 33);
      store v_9881 v_9889 4;
      v_9892 <- eval (isBitSet v_9888 1);
      v_9897 <- eval (eq (bv_xor (extract v_9882 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9882 v_9886) 27) (isBitSet v_9888 28)));
      setRegister cf (isBitClear v_9888 0);
      setRegister of (bit_and (eq v_9897 (isBitSet v_9886 0)) (notBool_ (eq v_9897 v_9892)));
      setRegister pf (parityFlag (extract v_9888 25 33));
      setRegister sf v_9892;
      setRegister zf (zeroFlag v_9889);
      pure ()
    pat_end;
    pattern fun (v_3249 : reg (bv 32)) (v_3248 : Mem) => do
      v_9915 <- evaluateAddress v_3248;
      v_9916 <- getRegister v_3249;
      v_9920 <- load v_9915 4;
      v_9922 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_9916 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_9920));
      v_9923 <- eval (extract v_9922 1 33);
      store v_9915 v_9923 4;
      v_9926 <- eval (isBitSet v_9922 1);
      v_9931 <- eval (eq (bv_xor (extract v_9916 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9916 v_9920) 27) (isBitSet v_9922 28)));
      setRegister cf (isBitClear v_9922 0);
      setRegister of (bit_and (eq v_9931 (isBitSet v_9920 0)) (notBool_ (eq v_9931 v_9926)));
      setRegister pf (parityFlag (extract v_9922 25 33));
      setRegister sf v_9926;
      setRegister zf (zeroFlag v_9923);
      pure ()
    pat_end

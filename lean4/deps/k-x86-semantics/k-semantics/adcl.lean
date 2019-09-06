def adcl1 : instruction :=
  definst "adcl" $ do
    pattern fun (v_2537 : imm int) (v_2539 : reg (bv 32)) => do
      v_4100 <- getRegister cf;
      v_4101 <- eval (handleImmediateWithSignExtend v_2537 32 32);
      v_4102 <- eval (concat (expression.bv_nat 1 0) v_4101);
      v_4105 <- getRegister v_2539;
      v_4107 <- eval (add (mux v_4100 (add v_4102 (expression.bv_nat 33 1)) v_4102) (concat (expression.bv_nat 1 0) v_4105));
      v_4108 <- eval (extract v_4107 1 33);
      setRegister (lhs.of_reg v_2539) v_4108;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4101 v_4105) 27) (isBitSet v_4107 28)));
      setRegister cf (isBitSet v_4107 0);
      setRegister of (overflowFlag v_4101 v_4105 v_4108);
      setRegister pf (parityFlag (extract v_4107 25 33));
      setRegister sf (isBitSet v_4107 1);
      setRegister zf (zeroFlag v_4108);
      pure ()
    pat_end;
    pattern fun (v_2547 : reg (bv 32)) (v_2548 : reg (bv 32)) => do
      v_4131 <- getRegister cf;
      v_4132 <- getRegister v_2547;
      v_4133 <- eval (concat (expression.bv_nat 1 0) v_4132);
      v_4136 <- getRegister v_2548;
      v_4138 <- eval (add (mux v_4131 (add v_4133 (expression.bv_nat 33 1)) v_4133) (concat (expression.bv_nat 1 0) v_4136));
      v_4139 <- eval (extract v_4138 1 33);
      setRegister (lhs.of_reg v_2548) v_4139;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4132 v_4136) 27) (isBitSet v_4138 28)));
      setRegister cf (isBitSet v_4138 0);
      setRegister of (overflowFlag v_4132 v_4136 v_4139);
      setRegister pf (parityFlag (extract v_4138 25 33));
      setRegister sf (isBitSet v_4138 1);
      setRegister zf (zeroFlag v_4139);
      pure ()
    pat_end;
    pattern fun (v_2542 : Mem) (v_2543 : reg (bv 32)) => do
      v_8584 <- getRegister cf;
      v_8585 <- evaluateAddress v_2542;
      v_8586 <- load v_8585 4;
      v_8587 <- eval (concat (expression.bv_nat 1 0) v_8586);
      v_8590 <- getRegister v_2543;
      v_8592 <- eval (add (mux v_8584 (add v_8587 (expression.bv_nat 33 1)) v_8587) (concat (expression.bv_nat 1 0) v_8590));
      v_8593 <- eval (extract v_8592 1 33);
      setRegister (lhs.of_reg v_2543) v_8593;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8586 v_8590) 27) (isBitSet v_8592 28)));
      setRegister cf (isBitSet v_8592 0);
      setRegister of (overflowFlag v_8586 v_8590 v_8593);
      setRegister pf (parityFlag (extract v_8592 25 33));
      setRegister sf (isBitSet v_8592 1);
      setRegister zf (zeroFlag v_8593);
      pure ()
    pat_end;
    pattern fun (v_2530 : imm int) (v_2529 : Mem) => do
      v_9888 <- evaluateAddress v_2529;
      v_9889 <- getRegister cf;
      v_9890 <- eval (handleImmediateWithSignExtend v_2530 32 32);
      v_9891 <- eval (concat (expression.bv_nat 1 0) v_9890);
      v_9894 <- load v_9888 4;
      v_9896 <- eval (add (mux v_9889 (add v_9891 (expression.bv_nat 33 1)) v_9891) (concat (expression.bv_nat 1 0) v_9894));
      v_9897 <- eval (extract v_9896 1 33);
      store v_9888 v_9897 4;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9890 v_9894) 27) (isBitSet v_9896 28)));
      setRegister cf (isBitSet v_9896 0);
      setRegister of (overflowFlag v_9890 v_9894 v_9897);
      setRegister pf (parityFlag (extract v_9896 25 33));
      setRegister sf (isBitSet v_9896 1);
      setRegister zf (zeroFlag v_9897);
      pure ()
    pat_end;
    pattern fun (v_2534 : reg (bv 32)) (v_2533 : Mem) => do
      v_9916 <- evaluateAddress v_2533;
      v_9917 <- getRegister cf;
      v_9918 <- getRegister v_2534;
      v_9919 <- eval (concat (expression.bv_nat 1 0) v_9918);
      v_9922 <- load v_9916 4;
      v_9924 <- eval (add (mux v_9917 (add v_9919 (expression.bv_nat 33 1)) v_9919) (concat (expression.bv_nat 1 0) v_9922));
      v_9925 <- eval (extract v_9924 1 33);
      store v_9916 v_9925 4;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9918 v_9922) 27) (isBitSet v_9924 28)));
      setRegister cf (isBitSet v_9924 0);
      setRegister of (overflowFlag v_9918 v_9922 v_9925);
      setRegister pf (parityFlag (extract v_9924 25 33));
      setRegister sf (isBitSet v_9924 1);
      setRegister zf (zeroFlag v_9925);
      pure ()
    pat_end

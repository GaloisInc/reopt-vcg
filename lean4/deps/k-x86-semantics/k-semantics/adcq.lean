def adcq1 : instruction :=
  definst "adcq" $ do
    pattern fun (v_2559 : imm int) (v_2560 : reg (bv 64)) => do
      v_4166 <- getRegister cf;
      v_4167 <- eval (handleImmediateWithSignExtend v_2559 32 32);
      v_4168 <- eval (sext v_4167 64);
      v_4169 <- eval (concat (expression.bv_nat 1 0) v_4168);
      v_4172 <- getRegister v_2560;
      v_4174 <- eval (add (mux v_4166 (add v_4169 (expression.bv_nat 65 1)) v_4169) (concat (expression.bv_nat 1 0) v_4172));
      v_4175 <- eval (extract v_4174 1 65);
      setRegister (lhs.of_reg v_2560) v_4175;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_4167 27) (isBitSet v_4172 59))) (isBitSet v_4174 60)));
      setRegister cf (isBitSet v_4174 0);
      setRegister of (overflowFlag v_4168 v_4172 v_4175);
      setRegister pf (parityFlag (extract v_4174 57 65));
      setRegister sf (isBitSet v_4174 1);
      setRegister zf (zeroFlag v_4175);
      pure ()
    pat_end;
    pattern fun (v_2568 : reg (bv 64)) (v_2569 : reg (bv 64)) => do
      v_4200 <- getRegister cf;
      v_4201 <- getRegister v_2568;
      v_4202 <- eval (concat (expression.bv_nat 1 0) v_4201);
      v_4205 <- getRegister v_2569;
      v_4207 <- eval (add (mux v_4200 (add v_4202 (expression.bv_nat 65 1)) v_4202) (concat (expression.bv_nat 1 0) v_4205));
      v_4208 <- eval (extract v_4207 1 65);
      setRegister (lhs.of_reg v_2569) v_4208;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4201 v_4205) 59) (isBitSet v_4207 60)));
      setRegister cf (isBitSet v_4207 0);
      setRegister of (overflowFlag v_4201 v_4205 v_4208);
      setRegister pf (parityFlag (extract v_4207 57 65));
      setRegister sf (isBitSet v_4207 1);
      setRegister zf (zeroFlag v_4208);
      pure ()
    pat_end;
    pattern fun (v_2564 : Mem) (v_2565 : reg (bv 64)) => do
      v_8614 <- getRegister cf;
      v_8615 <- evaluateAddress v_2564;
      v_8616 <- load v_8615 8;
      v_8617 <- eval (concat (expression.bv_nat 1 0) v_8616);
      v_8620 <- getRegister v_2565;
      v_8622 <- eval (add (mux v_8614 (add v_8617 (expression.bv_nat 65 1)) v_8617) (concat (expression.bv_nat 1 0) v_8620));
      v_8623 <- eval (extract v_8622 1 65);
      setRegister (lhs.of_reg v_2565) v_8623;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8616 v_8620) 59) (isBitSet v_8622 60)));
      setRegister cf (isBitSet v_8622 0);
      setRegister of (overflowFlag v_8616 v_8620 v_8623);
      setRegister pf (parityFlag (extract v_8622 57 65));
      setRegister sf (isBitSet v_8622 1);
      setRegister zf (zeroFlag v_8623);
      pure ()
    pat_end;
    pattern fun (v_2552 : imm int) (v_2551 : Mem) => do
      v_9944 <- evaluateAddress v_2551;
      v_9945 <- getRegister cf;
      v_9946 <- eval (handleImmediateWithSignExtend v_2552 32 32);
      v_9947 <- eval (sext v_9946 64);
      v_9948 <- eval (concat (expression.bv_nat 1 0) v_9947);
      v_9951 <- load v_9944 8;
      v_9953 <- eval (add (mux v_9945 (add v_9948 (expression.bv_nat 65 1)) v_9948) (concat (expression.bv_nat 1 0) v_9951));
      v_9954 <- eval (extract v_9953 1 65);
      store v_9944 v_9954 8;
      setRegister af (notBool_ (eq (notBool_ (eq (isBitSet v_9946 27) (isBitSet v_9951 59))) (isBitSet v_9953 60)));
      setRegister cf (isBitSet v_9953 0);
      setRegister of (overflowFlag v_9947 v_9951 v_9954);
      setRegister pf (parityFlag (extract v_9953 57 65));
      setRegister sf (isBitSet v_9953 1);
      setRegister zf (zeroFlag v_9954);
      pure ()
    pat_end;
    pattern fun (v_2556 : reg (bv 64)) (v_2555 : Mem) => do
      v_9975 <- evaluateAddress v_2555;
      v_9976 <- getRegister cf;
      v_9977 <- getRegister v_2556;
      v_9978 <- eval (concat (expression.bv_nat 1 0) v_9977);
      v_9981 <- load v_9975 8;
      v_9983 <- eval (add (mux v_9976 (add v_9978 (expression.bv_nat 65 1)) v_9978) (concat (expression.bv_nat 1 0) v_9981));
      v_9984 <- eval (extract v_9983 1 65);
      store v_9975 v_9984 8;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9977 v_9981) 59) (isBitSet v_9983 60)));
      setRegister cf (isBitSet v_9983 0);
      setRegister of (overflowFlag v_9977 v_9981 v_9984);
      setRegister pf (parityFlag (extract v_9983 57 65));
      setRegister sf (isBitSet v_9983 1);
      setRegister zf (zeroFlag v_9984);
      pure ()
    pat_end

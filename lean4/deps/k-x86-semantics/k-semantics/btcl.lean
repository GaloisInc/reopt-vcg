def btcl1 : instruction :=
  definst "btcl" $ do
    pattern fun (v_3109 : imm int) (v_3113 : reg (bv 32)) => do
      v_5837 <- getRegister v_3113;
      v_5840 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3109 8 8) (expression.bv_nat 8 31)) 32);
      setRegister (lhs.of_reg v_3113) (bv_xor v_5837 (extract (shl (expression.bv_nat 32 1) v_5840) 0 32));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5837 v_5840) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3117 : reg (bv 32)) (v_3118 : reg (bv 32)) => do
      v_5852 <- getRegister v_3118;
      v_5853 <- getRegister v_3117;
      v_5854 <- eval (bv_and v_5853 (expression.bv_nat 32 31));
      setRegister (lhs.of_reg v_3118) (bv_xor v_5852 (extract (shl (expression.bv_nat 32 1) v_5854) 0 32));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_5852 v_5854) 31);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3101 : imm int) (v_3104 : Mem) => do
      v_10463 <- evaluateAddress v_3104;
      v_10464 <- eval (handleImmediateWithSignExtend v_3101 8 8);
      v_10468 <- eval (add v_10463 (concat (expression.bv_nat 59 0) (bv_and (extract v_10464 0 5) (expression.bv_nat 5 3))));
      v_10469 <- load v_10468 1;
      v_10472 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10464 5 8) (expression.bv_nat 3 7)));
      store v_10468 (bv_xor v_10469 (extract (shl (expression.bv_nat 8 1) v_10472) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10469 v_10472) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3108 : reg (bv 32)) (v_3107 : Mem) => do
      v_10484 <- evaluateAddress v_3107;
      v_10485 <- getRegister v_3108;
      v_10489 <- eval (add v_10484 (concat (expression.bv_nat 3 0) (extract (sext v_10485 64) 0 61)));
      v_10490 <- load v_10489 1;
      v_10492 <- eval (concat (expression.bv_nat 5 0) (extract v_10485 29 32));
      store v_10489 (bv_xor v_10490 (extract (shl (expression.bv_nat 8 1) v_10492) 0 8)) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10490 v_10492) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end

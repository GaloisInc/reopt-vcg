def adcb1 : instruction :=
  definst "adcb" $ do
    pattern fun (v_2504 : imm int) (v_2507 : reg (bv 8)) => do
      v_3975 <- getRegister cf;
      v_3976 <- eval (handleImmediateWithSignExtend v_2504 8 8);
      v_3977 <- eval (concat (expression.bv_nat 1 0) v_3976);
      v_3980 <- getRegister v_2507;
      v_3982 <- eval (add (mux v_3975 (add v_3977 (expression.bv_nat 9 1)) v_3977) (concat (expression.bv_nat 1 0) v_3980));
      v_3983 <- eval (extract v_3982 1 9);
      setRegister (lhs.of_reg v_2507) v_3983;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_3976 v_3980) 3) (isBitSet v_3982 4)));
      setRegister cf (isBitSet v_3982 0);
      setRegister of (overflowFlag v_3976 v_3980 v_3983);
      setRegister pf (parityFlag v_3983);
      setRegister sf (isBitSet v_3982 1);
      setRegister zf (zeroFlag v_3983);
      pure ()
    pat_end;
    pattern fun (v_2520 : reg (bv 8)) (v_2521 : reg (bv 8)) => do
      v_4031 <- getRegister cf;
      v_4032 <- getRegister v_2520;
      v_4033 <- eval (concat (expression.bv_nat 1 0) v_4032);
      v_4036 <- getRegister v_2521;
      v_4038 <- eval (add (mux v_4031 (add v_4033 (expression.bv_nat 9 1)) v_4033) (concat (expression.bv_nat 1 0) v_4036));
      v_4039 <- eval (extract v_4038 1 9);
      setRegister (lhs.of_reg v_2521) v_4039;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_4032 v_4036) 3) (isBitSet v_4038 4)));
      setRegister cf (isBitSet v_4038 0);
      setRegister of (overflowFlag v_4032 v_4036 v_4039);
      setRegister pf (parityFlag v_4039);
      setRegister sf (isBitSet v_4038 1);
      setRegister zf (zeroFlag v_4039);
      pure ()
    pat_end;
    pattern fun (v_2511 : Mem) (v_2512 : reg (bv 8)) => do
      v_8555 <- getRegister cf;
      v_8556 <- evaluateAddress v_2511;
      v_8557 <- load v_8556 1;
      v_8558 <- eval (concat (expression.bv_nat 1 0) v_8557);
      v_8561 <- getRegister v_2512;
      v_8563 <- eval (add (mux v_8555 (add v_8558 (expression.bv_nat 9 1)) v_8558) (concat (expression.bv_nat 1 0) v_8561));
      v_8564 <- eval (extract v_8563 1 9);
      setRegister (lhs.of_reg v_2512) v_8564;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_8557 v_8561) 3) (isBitSet v_8563 4)));
      setRegister cf (isBitSet v_8563 0);
      setRegister of (overflowFlag v_8557 v_8561 v_8564);
      setRegister pf (parityFlag v_8564);
      setRegister sf (isBitSet v_8563 1);
      setRegister zf (zeroFlag v_8564);
      pure ()
    pat_end;
    pattern fun (v_2473 : imm int) (v_2476 : Mem) => do
      v_9807 <- evaluateAddress v_2476;
      v_9808 <- getRegister cf;
      v_9809 <- eval (handleImmediateWithSignExtend v_2473 8 8);
      v_9810 <- eval (concat (expression.bv_nat 1 0) v_9809);
      v_9813 <- load v_9807 1;
      v_9815 <- eval (add (mux v_9808 (add v_9810 (expression.bv_nat 9 1)) v_9810) (concat (expression.bv_nat 1 0) v_9813));
      v_9816 <- eval (extract v_9815 1 9);
      store v_9807 v_9816 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9809 v_9813) 3) (isBitSet v_9815 4)));
      setRegister cf (isBitSet v_9815 0);
      setRegister of (overflowFlag v_9809 v_9813 v_9816);
      setRegister pf (parityFlag v_9816);
      setRegister sf (isBitSet v_9815 1);
      setRegister zf (zeroFlag v_9816);
      pure ()
    pat_end;
    pattern fun (v_2484 : reg (bv 8)) (v_2483 : Mem) => do
      v_9861 <- evaluateAddress v_2483;
      v_9862 <- getRegister cf;
      v_9863 <- getRegister v_2484;
      v_9864 <- eval (concat (expression.bv_nat 1 0) v_9863);
      v_9867 <- load v_9861 1;
      v_9869 <- eval (add (mux v_9862 (add v_9864 (expression.bv_nat 9 1)) v_9864) (concat (expression.bv_nat 1 0) v_9867));
      v_9870 <- eval (extract v_9869 1 9);
      store v_9861 v_9870 1;
      setRegister af (notBool_ (eq (isBitSet (bv_xor v_9863 v_9867) 3) (isBitSet v_9869 4)));
      setRegister cf (isBitSet v_9869 0);
      setRegister of (overflowFlag v_9863 v_9867 v_9870);
      setRegister pf (parityFlag v_9870);
      setRegister sf (isBitSet v_9869 1);
      setRegister zf (zeroFlag v_9870);
      pure ()
    pat_end

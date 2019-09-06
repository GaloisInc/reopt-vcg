def shll1 : instruction :=
  definst "shll" $ do
    pattern fun (_ : clReg) (v_2847 : reg (bv 32)) => do
      v_4501 <- getRegister rcx;
      v_4503 <- eval (bv_and (extract v_4501 56 64) (expression.bv_nat 8 31));
      v_4504 <- eval (eq v_4503 (expression.bv_nat 8 0));
      v_4505 <- getRegister zf;
      v_4506 <- getRegister v_2847;
      v_4510 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4506) (concat (expression.bv_nat 25 0) v_4503)) 0 33);
      v_4511 <- eval (extract v_4510 1 33);
      v_4514 <- getRegister sf;
      v_4515 <- eval (isBitSet v_4510 1);
      v_4517 <- getRegister pf;
      v_4523 <- getRegister cf;
      v_4526 <- eval (mux (uge v_4503 (expression.bv_nat 8 32)) undef (mux v_4504 v_4523 (isBitSet v_4510 0)));
      v_4529 <- getRegister of;
      v_4532 <- getRegister af;
      setRegister (lhs.of_reg v_2847) v_4511;
      setRegister af (mux v_4504 v_4532 undef);
      setRegister cf v_4526;
      setRegister of (mux (eq v_4503 (expression.bv_nat 8 1)) (notBool_ (eq v_4526 v_4515)) (mux v_4504 v_4529 undef));
      setRegister pf (mux v_4504 v_4517 (parityFlag (extract v_4510 25 33)));
      setRegister sf (mux v_4504 v_4514 v_4515);
      setRegister zf (mux v_4504 v_4505 (eq v_4511 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2851 : imm int) (v_2852 : reg (bv 32)) => do
      v_4542 <- eval (bv_and (handleImmediateWithSignExtend v_2851 8 8) (expression.bv_nat 8 31));
      v_4543 <- eval (eq v_4542 (expression.bv_nat 8 0));
      v_4544 <- getRegister zf;
      v_4545 <- getRegister v_2852;
      v_4549 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_4545) (concat (expression.bv_nat 25 0) v_4542)) 0 33);
      v_4550 <- eval (extract v_4549 1 33);
      v_4553 <- getRegister sf;
      v_4554 <- eval (isBitSet v_4549 1);
      v_4556 <- getRegister pf;
      v_4562 <- getRegister cf;
      v_4565 <- eval (mux (uge v_4542 (expression.bv_nat 8 32)) undef (mux v_4543 v_4562 (isBitSet v_4549 0)));
      v_4568 <- getRegister of;
      v_4571 <- getRegister af;
      setRegister (lhs.of_reg v_2852) v_4550;
      setRegister af (mux v_4543 v_4571 undef);
      setRegister cf v_4565;
      setRegister of (mux (eq v_4542 (expression.bv_nat 8 1)) (notBool_ (eq v_4565 v_4554)) (mux v_4543 v_4568 undef));
      setRegister pf (mux v_4543 v_4556 (parityFlag (extract v_4549 25 33)));
      setRegister sf (mux v_4543 v_4553 v_4554);
      setRegister zf (mux v_4543 v_4544 (eq v_4550 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (_ : clReg) (v_2837 : Mem) => do
      v_8937 <- evaluateAddress v_2837;
      v_8938 <- load v_8937 4;
      v_8940 <- getRegister rcx;
      v_8942 <- eval (bv_and (extract v_8940 56 64) (expression.bv_nat 8 31));
      v_8945 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_8938) (concat (expression.bv_nat 25 0) v_8942)) 0 33);
      v_8946 <- eval (extract v_8945 1 33);
      store v_8937 v_8946 4;
      v_8948 <- eval (eq v_8942 (expression.bv_nat 8 0));
      v_8949 <- getRegister zf;
      v_8952 <- getRegister sf;
      v_8953 <- eval (isBitSet v_8945 1);
      v_8955 <- getRegister pf;
      v_8961 <- getRegister cf;
      v_8964 <- eval (mux (uge v_8942 (expression.bv_nat 8 32)) undef (mux v_8948 v_8961 (isBitSet v_8945 0)));
      v_8967 <- getRegister of;
      v_8970 <- getRegister af;
      setRegister af (mux v_8948 v_8970 undef);
      setRegister cf v_8964;
      setRegister of (mux (eq v_8942 (expression.bv_nat 8 1)) (notBool_ (eq v_8964 v_8953)) (mux v_8948 v_8967 undef));
      setRegister pf (mux v_8948 v_8955 (parityFlag (extract v_8945 25 33)));
      setRegister sf (mux v_8948 v_8952 v_8953);
      setRegister zf (mux v_8948 v_8949 (eq v_8946 (expression.bv_nat 32 0)));
      pure ()
    pat_end;
    pattern fun (v_2841 : imm int) (v_2840 : Mem) => do
      v_8978 <- evaluateAddress v_2840;
      v_8979 <- load v_8978 4;
      v_8982 <- eval (bv_and (handleImmediateWithSignExtend v_2841 8 8) (expression.bv_nat 8 31));
      v_8985 <- eval (extract (shl (concat (expression.bv_nat 1 0) v_8979) (concat (expression.bv_nat 25 0) v_8982)) 0 33);
      v_8986 <- eval (extract v_8985 1 33);
      store v_8978 v_8986 4;
      v_8988 <- eval (eq v_8982 (expression.bv_nat 8 0));
      v_8989 <- getRegister zf;
      v_8992 <- getRegister sf;
      v_8993 <- eval (isBitSet v_8985 1);
      v_8995 <- getRegister pf;
      v_9001 <- getRegister cf;
      v_9004 <- eval (mux (uge v_8982 (expression.bv_nat 8 32)) undef (mux v_8988 v_9001 (isBitSet v_8985 0)));
      v_9007 <- getRegister of;
      v_9010 <- getRegister af;
      setRegister af (mux v_8988 v_9010 undef);
      setRegister cf v_9004;
      setRegister of (mux (eq v_8982 (expression.bv_nat 8 1)) (notBool_ (eq v_9004 v_8993)) (mux v_8988 v_9007 undef));
      setRegister pf (mux v_8988 v_8995 (parityFlag (extract v_8985 25 33)));
      setRegister sf (mux v_8988 v_8992 v_8993);
      setRegister zf (mux v_8988 v_8989 (eq v_8986 (expression.bv_nat 32 0)));
      pure ()
    pat_end

def orq1 : instruction :=
  definst "orq" $ do
    pattern fun (v_3089 : imm int) (v_3088 : reg (bv 64)) => do
      v_4862 <- getRegister v_3088;
      v_4863 <- eval (handleImmediateWithSignExtend v_3089 32 32);
      v_4865 <- eval (bv_or v_4862 (sext v_4863 64));
      setRegister (lhs.of_reg v_3088) v_4865;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4862 63 64) (extract v_4863 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4862 62 63) (extract v_4863 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4862 61 62) (extract v_4863 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4862 60 61) (extract v_4863 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4862 59 60) (extract v_4863 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4862 58 59) (extract v_4863 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4862 57 58) (extract v_4863 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4862 56 57) (extract v_4863 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_4865 0);
      setRegister zf (zeroFlag v_4865);
      pure ()
    pat_end;
    pattern fun (v_3097 : reg (bv 64)) (v_3098 : reg (bv 64)) => do
      v_4924 <- getRegister v_3098;
      v_4925 <- getRegister v_3097;
      v_4926 <- eval (bv_or v_4924 v_4925);
      setRegister (lhs.of_reg v_3098) v_4926;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4926 56 64));
      setRegister sf (isBitSet v_4926 0);
      setRegister zf (zeroFlag v_4926);
      pure ()
    pat_end;
    pattern fun (v_3093 : Mem) (v_3094 : reg (bv 64)) => do
      v_9026 <- getRegister v_3094;
      v_9027 <- evaluateAddress v_3093;
      v_9028 <- load v_9027 8;
      v_9029 <- eval (bv_or v_9026 v_9028);
      setRegister (lhs.of_reg v_3094) v_9029;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9029 56 64));
      setRegister sf (isBitSet v_9029 0);
      setRegister zf (zeroFlag v_9029);
      pure ()
    pat_end;
    pattern fun (v_3081 : imm int) (v_3080 : Mem) => do
      v_10903 <- evaluateAddress v_3080;
      v_10904 <- load v_10903 8;
      v_10905 <- eval (handleImmediateWithSignExtend v_3081 32 32);
      v_10907 <- eval (bv_or v_10904 (sext v_10905 64));
      store v_10903 v_10907 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_10904 63 64) (extract v_10905 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_10904 62 63) (extract v_10905 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10904 61 62) (extract v_10905 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10904 60 61) (extract v_10905 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10904 59 60) (extract v_10905 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10904 58 59) (extract v_10905 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10904 57 58) (extract v_10905 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10904 56 57) (extract v_10905 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_10907 0);
      setRegister zf (zeroFlag v_10907);
      pure ()
    pat_end;
    pattern fun (v_3085 : reg (bv 64)) (v_3084 : Mem) => do
      v_10962 <- evaluateAddress v_3084;
      v_10963 <- load v_10962 8;
      v_10964 <- getRegister v_3085;
      v_10965 <- eval (bv_or v_10963 v_10964);
      store v_10962 v_10965 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10965 56 64));
      setRegister sf (isBitSet v_10965 0);
      setRegister zf (zeroFlag v_10965);
      pure ()
    pat_end

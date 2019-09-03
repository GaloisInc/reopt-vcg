def orq1 : instruction :=
  definst "orq" $ do
    pattern fun (v_3000 : imm int) (v_3001 : reg (bv 64)) => do
      v_4830 <- getRegister v_3001;
      v_4831 <- eval (handleImmediateWithSignExtend v_3000 32 32);
      v_4834 <- eval (bv_or v_4830 (mi 64 (svalueMInt v_4831)));
      setRegister (lhs.of_reg v_3001) v_4834;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4830 63 64) (extract v_4831 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4830 62 63) (extract v_4831 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4830 61 62) (extract v_4831 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4830 60 61) (extract v_4831 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4830 59 60) (extract v_4831 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4830 58 59) (extract v_4831 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4830 57 58) (extract v_4831 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4830 56 57) (extract v_4831 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_4834);
      setRegister sf (extract v_4834 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3009 : reg (bv 64)) (v_3010 : reg (bv 64)) => do
      v_4894 <- getRegister v_3010;
      v_4895 <- getRegister v_3009;
      v_4896 <- eval (bv_or v_4894 v_4895);
      setRegister (lhs.of_reg v_3010) v_4896;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_4896 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_4896);
      setRegister sf (extract v_4896 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3014 : imm int) rax => do
      v_4908 <- getRegister rax;
      v_4909 <- eval (handleImmediateWithSignExtend v_3014 32 32);
      v_4912 <- eval (bv_or v_4908 (mi 64 (svalueMInt v_4909)));
      setRegister rax v_4912;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4908 63 64) (extract v_4909 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4908 62 63) (extract v_4909 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4908 61 62) (extract v_4909 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4908 60 61) (extract v_4909 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4908 59 60) (extract v_4909 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4908 58 59) (extract v_4909 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4908 57 58) (extract v_4909 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4908 56 57) (extract v_4909 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4912);
      setRegister af undef;
      setRegister sf (extract v_4912 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3004 : Mem) (v_3005 : reg (bv 64)) => do
      v_9160 <- getRegister v_3005;
      v_9161 <- evaluateAddress v_3004;
      v_9162 <- load v_9161 8;
      v_9163 <- eval (bv_or v_9160 v_9162);
      setRegister (lhs.of_reg v_3005) v_9163;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9163 56 64));
      setRegister zf (zeroFlag v_9163);
      setRegister af undef;
      setRegister sf (extract v_9163 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2992 : imm int) (v_2991 : Mem) => do
      v_11237 <- evaluateAddress v_2991;
      v_11238 <- load v_11237 8;
      v_11239 <- eval (handleImmediateWithSignExtend v_2992 32 32);
      v_11242 <- eval (bv_or v_11238 (mi 64 (svalueMInt v_11239)));
      store v_11237 v_11242 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_11238 63 64) (extract v_11239 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_11238 62 63) (extract v_11239 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11238 61 62) (extract v_11239 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11238 60 61) (extract v_11239 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11238 59 60) (extract v_11239 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11238 58 59) (extract v_11239 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11238 57 58) (extract v_11239 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_11238 56 57) (extract v_11239 24 25)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (zeroFlag v_11242);
      setRegister sf (extract v_11242 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2996 : reg (bv 64)) (v_2995 : Mem) => do
      v_11298 <- evaluateAddress v_2995;
      v_11299 <- load v_11298 8;
      v_11300 <- getRegister v_2996;
      v_11301 <- eval (bv_or v_11299 v_11300);
      store v_11298 v_11301 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11301 56 64));
      setRegister af undef;
      setRegister zf (zeroFlag v_11301);
      setRegister sf (extract v_11301 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end

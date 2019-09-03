def cmpq1 : instruction :=
  definst "cmpq" $ do
    pattern fun (v_2399 : imm int) (v_2401 : reg (bv 64)) => do
      v_3753 <- eval (handleImmediateWithSignExtend v_2399 32 32);
      v_3754 <- eval (leanSignExtend v_3753 64);
      v_3758 <- getRegister v_2401;
      v_3760 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3754 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3758));
      v_3765 <- eval (extract v_3760 1 2);
      v_3777 <- eval (eq (bv_xor (extract v_3754 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3777 (eq (extract v_3758 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3777 (eq v_3765 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3760 57 65));
      setRegister af (bv_xor (bv_xor (extract v_3753 27 28) (extract v_3758 59 60)) (extract v_3760 60 61));
      setRegister zf (zeroFlag (extract v_3760 1 65));
      setRegister sf v_3765;
      setRegister cf (mux (notBool_ (eq (extract v_3760 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2409 : reg (bv 64)) (v_2410 : reg (bv 64)) => do
      v_3796 <- getRegister v_2409;
      v_3800 <- getRegister v_2410;
      v_3802 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3796 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3800));
      v_3807 <- eval (extract v_3802 1 2);
      v_3818 <- eval (eq (bv_xor (extract v_3796 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3818 (eq (extract v_3800 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3818 (eq v_3807 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3802 57 65));
      setRegister af (bv_xor (extract (bv_xor v_3796 v_3800) 59 60) (extract v_3802 60 61));
      setRegister zf (zeroFlag (extract v_3802 1 65));
      setRegister sf v_3807;
      setRegister cf (mux (notBool_ (eq (extract v_3802 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2392 : imm int) (v_2391 : Mem) => do
      v_8021 <- eval (handleImmediateWithSignExtend v_2392 32 32);
      v_8022 <- eval (leanSignExtend v_8021 64);
      v_8026 <- evaluateAddress v_2391;
      v_8027 <- load v_8026 8;
      v_8029 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8022 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_8027));
      v_8034 <- eval (extract v_8029 1 2);
      v_8046 <- eval (eq (bv_xor (extract v_8022 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8046 (eq (extract v_8027 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8046 (eq v_8034 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8029 57 65));
      setRegister af (bv_xor (bv_xor (extract v_8021 27 28) (extract v_8027 59 60)) (extract v_8029 60 61));
      setRegister zf (zeroFlag (extract v_8029 1 65));
      setRegister sf v_8034;
      setRegister cf (mux (notBool_ (eq (extract v_8029 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2396 : reg (bv 64)) (v_2395 : Mem) => do
      v_8061 <- getRegister v_2396;
      v_8065 <- evaluateAddress v_2395;
      v_8066 <- load v_8065 8;
      v_8068 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8061 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_8066));
      v_8073 <- eval (extract v_8068 1 2);
      v_8084 <- eval (eq (bv_xor (extract v_8061 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8084 (eq (extract v_8066 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8084 (eq v_8073 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8068 57 65));
      setRegister af (bv_xor (extract (bv_xor v_8061 v_8066) 59 60) (extract v_8068 60 61));
      setRegister zf (zeroFlag (extract v_8068 1 65));
      setRegister sf v_8073;
      setRegister cf (mux (notBool_ (eq (extract v_8068 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2404 : Mem) (v_2405 : reg (bv 64)) => do
      v_8099 <- evaluateAddress v_2404;
      v_8100 <- load v_8099 8;
      v_8104 <- getRegister v_2405;
      v_8106 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8100 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_8104));
      v_8111 <- eval (extract v_8106 1 2);
      v_8122 <- eval (eq (bv_xor (extract v_8100 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8122 (eq (extract v_8104 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8122 (eq v_8111 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_8106 57 65));
      setRegister af (bv_xor (extract (bv_xor v_8100 v_8104) 59 60) (extract v_8106 60 61));
      setRegister zf (zeroFlag (extract v_8106 1 65));
      setRegister sf v_8111;
      setRegister cf (mux (notBool_ (eq (extract v_8106 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

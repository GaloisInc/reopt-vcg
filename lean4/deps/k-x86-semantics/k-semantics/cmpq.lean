def cmpq1 : instruction :=
  definst "cmpq" $ do
    pattern fun (v_2389 : imm int) (v_2388 : reg (bv 64)) => do
      v_3740 <- eval (handleImmediateWithSignExtend v_2389 32 32);
      v_3742 <- eval (mi 64 (svalueMInt v_3740));
      v_3748 <- getRegister v_2388;
      v_3750 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3742 (mi (bitwidthMInt v_3742) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3748));
      v_3755 <- eval (extract v_3750 1 2);
      v_3765 <- eval (extract v_3742 0 1);
      v_3769 <- eval (eq (bv_xor v_3765 (mi (bitwidthMInt v_3765) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3769 (eq (extract v_3748 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3769 (eq v_3755 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3750 57 65));
      setRegister af (bv_xor (bv_xor (extract v_3740 27 28) (extract v_3748 59 60)) (extract v_3750 60 61));
      setRegister zf (zeroFlag (extract v_3750 1 65));
      setRegister sf v_3755;
      setRegister cf (mux (notBool_ (eq (extract v_3750 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2397 : reg (bv 64)) (v_2398 : reg (bv 64)) => do
      v_3788 <- getRegister v_2397;
      v_3794 <- getRegister v_2398;
      v_3796 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_3788 (mi (bitwidthMInt v_3788) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_3794));
      v_3801 <- eval (extract v_3796 1 2);
      v_3810 <- eval (extract v_3788 0 1);
      v_3814 <- eval (eq (bv_xor v_3810 (mi (bitwidthMInt v_3810) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_3814 (eq (extract v_3794 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3814 (eq v_3801 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_3796 57 65));
      setRegister af (bv_xor (extract (bv_xor v_3788 v_3794) 59 60) (extract v_3796 60 61));
      setRegister zf (zeroFlag (extract v_3796 1 65));
      setRegister sf v_3801;
      setRegister cf (mux (notBool_ (eq (extract v_3796 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2381 : imm int) (v_2380 : Mem) => do
      v_7724 <- eval (handleImmediateWithSignExtend v_2381 32 32);
      v_7726 <- eval (mi 64 (svalueMInt v_7724));
      v_7732 <- evaluateAddress v_2380;
      v_7733 <- load v_7732 8;
      v_7735 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7726 (mi (bitwidthMInt v_7726) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7733));
      v_7740 <- eval (extract v_7735 1 2);
      v_7750 <- eval (extract v_7726 0 1);
      v_7754 <- eval (eq (bv_xor v_7750 (mi (bitwidthMInt v_7750) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_7754 (eq (extract v_7733 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7754 (eq v_7740 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7735 57 65));
      setRegister af (bv_xor (bv_xor (extract v_7724 27 28) (extract v_7733 59 60)) (extract v_7735 60 61));
      setRegister zf (zeroFlag (extract v_7735 1 65));
      setRegister sf v_7740;
      setRegister cf (mux (notBool_ (eq (extract v_7735 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2385 : reg (bv 64)) (v_2384 : Mem) => do
      v_7769 <- getRegister v_2385;
      v_7775 <- evaluateAddress v_2384;
      v_7776 <- load v_7775 8;
      v_7778 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7769 (mi (bitwidthMInt v_7769) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7776));
      v_7783 <- eval (extract v_7778 1 2);
      v_7792 <- eval (extract v_7769 0 1);
      v_7796 <- eval (eq (bv_xor v_7792 (mi (bitwidthMInt v_7792) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_7796 (eq (extract v_7776 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7796 (eq v_7783 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7778 57 65));
      setRegister af (bv_xor (extract (bv_xor v_7769 v_7776) 59 60) (extract v_7778 60 61));
      setRegister zf (zeroFlag (extract v_7778 1 65));
      setRegister sf v_7783;
      setRegister cf (mux (notBool_ (eq (extract v_7778 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2393 : Mem) (v_2394 : reg (bv 64)) => do
      v_7811 <- evaluateAddress v_2393;
      v_7812 <- load v_7811 8;
      v_7818 <- getRegister v_2394;
      v_7820 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7812 (mi (bitwidthMInt v_7812) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7818));
      v_7825 <- eval (extract v_7820 1 2);
      v_7834 <- eval (extract v_7812 0 1);
      v_7838 <- eval (eq (bv_xor v_7834 (mi (bitwidthMInt v_7834) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_7838 (eq (extract v_7818 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7838 (eq v_7825 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7820 57 65));
      setRegister af (bv_xor (extract (bv_xor v_7812 v_7818) 59 60) (extract v_7820 60 61));
      setRegister zf (zeroFlag (extract v_7820 1 65));
      setRegister sf v_7825;
      setRegister cf (mux (notBool_ (eq (extract v_7820 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

def xorl1 : instruction :=
  definst "xorl" $ do
    pattern fun (v_2766 : imm int) eax => do
      v_4832 <- getRegister rax;
      v_4834 <- eval (handleImmediateWithSignExtend v_2766 32 32);
      v_4838 <- eval (bv_xor (extract v_4832 32 64) v_4834);
      setRegister eax v_4838;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_4832 63 64) (extract v_4834 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_4832 62 63) (extract v_4834 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4832 61 62) (extract v_4834 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4832 60 61) (extract v_4834 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4832 59 60) (extract v_4834 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4832 58 59) (extract v_4834 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4832 57 58) (extract v_4834 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4832 56 57) (extract v_4834 24 25)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_4838 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf (bv_xor (extract v_4832 32 33) (extract v_4834 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2779 : imm int) (v_2777 : reg (bv 32)) => do
      v_4904 <- getRegister v_2777;
      v_4906 <- eval (handleImmediateWithSignExtend v_2779 32 32);
      v_4909 <- eval (bv_xor v_4904 v_4906);
      setRegister (lhs.of_reg v_2777) v_4909;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_4904 31 32) (extract v_4906 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_4904 30 31) (extract v_4906 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4904 29 30) (extract v_4906 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4904 28 29) (extract v_4906 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4904 27 28) (extract v_4906 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4904 26 27) (extract v_4906 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4904 25 26) (extract v_4906 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4904 24 25) (extract v_4906 24 25)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_4909 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf (bv_xor (extract v_4904 0 1) (extract v_4906 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2786 : reg (bv 32)) (v_2787 : reg (bv 32)) => do
      v_4971 <- getRegister v_2787;
      v_4973 <- getRegister v_2786;
      v_4976 <- eval (bv_xor v_4971 v_4973);
      setRegister (lhs.of_reg v_2787) v_4976;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_4971 31 32) (extract v_4973 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_4971 30 31) (extract v_4973 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4971 29 30) (extract v_4973 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4971 28 29) (extract v_4973 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4971 27 28) (extract v_4973 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4971 26 27) (extract v_4973 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4971 25 26) (extract v_4973 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_4971 24 25) (extract v_4973 24 25)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_4976 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf (bv_xor (extract v_4971 0 1) (extract v_4973 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2783 : Mem) (v_2782 : reg (bv 32)) => do
      v_7182 <- getRegister v_2782;
      v_7184 <- evaluateAddress v_2783;
      v_7185 <- load v_7184 4;
      v_7188 <- eval (bv_xor v_7182 v_7185);
      setRegister (lhs.of_reg v_2782) v_7188;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7182 31 32) (extract v_7185 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7182 30 31) (extract v_7185 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7182 29 30) (extract v_7185 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7182 28 29) (extract v_7185 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7182 27 28) (extract v_7185 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7182 26 27) (extract v_7185 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7182 25 26) (extract v_7185 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7182 24 25) (extract v_7185 24 25)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_7188 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf (bv_xor (extract v_7182 0 1) (extract v_7185 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2770 : imm int) (v_2769 : Mem) => do
      v_7786 <- evaluateAddress v_2769;
      v_7787 <- load v_7786 4;
      v_7788 <- eval (handleImmediateWithSignExtend v_2770 32 32);
      v_7789 <- eval (bv_xor v_7787 v_7788);
      store v_7786 v_7789 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7787 31 32) (extract v_7788 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7787 30 31) (extract v_7788 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7787 29 30) (extract v_7788 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7787 28 29) (extract v_7788 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7787 27 28) (extract v_7788 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7787 26 27) (extract v_7788 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7787 25 26) (extract v_7788 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7787 24 25) (extract v_7788 24 25)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_7789 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_7787 0 1) (extract v_7788 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2773 : reg (bv 32)) (v_2774 : Mem) => do
      v_7850 <- evaluateAddress v_2774;
      v_7851 <- load v_7850 4;
      v_7852 <- getRegister v_2773;
      v_7853 <- eval (bv_xor v_7851 v_7852);
      store v_7850 v_7853 4;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7851 31 32) (extract v_7852 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7851 30 31) (extract v_7852 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7851 29 30) (extract v_7852 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7851 28 29) (extract v_7852 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7851 27 28) (extract v_7852 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7851 26 27) (extract v_7852 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7851 25 26) (extract v_7852 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7851 24 25) (extract v_7852 24 25)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_7853 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_7851 0 1) (extract v_7852 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end

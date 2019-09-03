def xorq1 : instruction :=
  definst "xorq" $ do
    pattern fun (v_2818 : imm int) (v_2817 : reg (bv 64)) => do
      v_5058 <- getRegister v_2817;
      v_5060 <- eval (handleImmediateWithSignExtend v_2818 32 32);
      v_5062 <- eval (mi 64 (svalueMInt v_5060));
      v_5065 <- eval (bv_xor v_5058 v_5062);
      setRegister (lhs.of_reg v_2817) v_5065;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_5058 63 64) (extract v_5060 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_5058 62 63) (extract v_5060 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5058 61 62) (extract v_5060 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5058 60 61) (extract v_5060 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5058 59 60) (extract v_5060 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5058 58 59) (extract v_5060 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5058 57 58) (extract v_5060 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5058 56 57) (extract v_5060 24 25)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_5065 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf (bv_xor (extract v_5058 0 1) (extract v_5062 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2826 : reg (bv 64)) (v_2827 : reg (bv 64)) => do
      v_5127 <- getRegister v_2827;
      v_5129 <- getRegister v_2826;
      v_5132 <- eval (bv_xor v_5127 v_5129);
      setRegister (lhs.of_reg v_2827) v_5132;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_5127 63 64) (extract v_5129 63 64)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_5127 62 63) (extract v_5129 62 63)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5127 61 62) (extract v_5129 61 62)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5127 60 61) (extract v_5129 60 61)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5127 59 60) (extract v_5129 59 60)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5127 58 59) (extract v_5129 58 59)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5127 57 58) (extract v_5129 57 58)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_5127 56 57) (extract v_5129 56 57)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_5132 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister sf (bv_xor (extract v_5127 0 1) (extract v_5129 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2823 : Mem) (v_2822 : reg (bv 64)) => do
      v_7258 <- getRegister v_2822;
      v_7260 <- evaluateAddress v_2823;
      v_7261 <- load v_7260 8;
      v_7264 <- eval (bv_xor v_7258 v_7261);
      setRegister (lhs.of_reg v_2822) v_7264;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7258 63 64) (extract v_7261 63 64)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7258 62 63) (extract v_7261 62 63)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7258 61 62) (extract v_7261 61 62)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7258 60 61) (extract v_7261 60 61)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7258 59 60) (extract v_7261 59 60)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7258 58 59) (extract v_7261 58 59)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7258 57 58) (extract v_7261 57 58)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7258 56 57) (extract v_7261 56 57)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_7264 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_7258 0 1) (extract v_7261 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2810 : imm int) (v_2809 : Mem) => do
      v_7914 <- evaluateAddress v_2809;
      v_7915 <- load v_7914 8;
      v_7916 <- eval (handleImmediateWithSignExtend v_2810 32 32);
      v_7918 <- eval (mi 64 (svalueMInt v_7916));
      v_7919 <- eval (bv_xor v_7915 v_7918);
      store v_7914 v_7919 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7915 63 64) (extract v_7916 31 32)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7915 62 63) (extract v_7916 30 31)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7915 61 62) (extract v_7916 29 30)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7915 60 61) (extract v_7916 28 29)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7915 59 60) (extract v_7916 27 28)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7915 58 59) (extract v_7916 26 27)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7915 57 58) (extract v_7916 25 26)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7915 56 57) (extract v_7916 24 25)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_7919 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_7915 0 1) (extract v_7918 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_2813 : reg (bv 64)) (v_2814 : Mem) => do
      v_7980 <- evaluateAddress v_2814;
      v_7981 <- load v_7980 8;
      v_7982 <- getRegister v_2813;
      v_7983 <- eval (bv_xor v_7981 v_7982);
      store v_7980 v_7983 8;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_xor (extract v_7981 63 64) (extract v_7982 63 64)) (expression.bv_nat 1 1)) (eq (bv_xor (extract v_7981 62 63) (extract v_7982 62 63)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7981 61 62) (extract v_7982 61 62)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7981 60 61) (extract v_7982 60 61)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7981 59 60) (extract v_7982 59 60)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7981 58 59) (extract v_7982 58 59)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7981 57 58) (extract v_7982 57 58)) (expression.bv_nat 1 1)))) (eq (bv_xor (extract v_7981 56 57) (extract v_7982 56 57)) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af undef;
      setRegister zf (mux (eq v_7983 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf (bv_xor (extract v_7981 0 1) (extract v_7982 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end

def imulb1 : instruction :=
  definst "imulb" $ do
    pattern fun (v_2881 : reg (bv 8)) => do
      v_4990 <- getRegister v_2881;
      v_4993 <- getRegister rax;
      v_4997 <- eval (mul (mi 16 (svalueMInt v_4990)) (mi 16 (svalueMInt (extract v_4993 56 64))));
      v_5003 <- eval (mux (notBool_ (eq v_4997 (mi 16 (svalueMInt (extract v_4997 8 16))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rax (concat (extract v_4993 0 48) v_4997);
      setRegister of v_5003;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5003;
      pure ()
    pat_end;
    pattern fun (v_2878 : Mem) => do
      v_8648 <- evaluateAddress v_2878;
      v_8649 <- load v_8648 1;
      v_8652 <- getRegister rax;
      v_8656 <- eval (mul (mi 16 (svalueMInt v_8649)) (mi 16 (svalueMInt (extract v_8652 56 64))));
      v_8662 <- eval (mux (notBool_ (eq v_8656 (mi 16 (svalueMInt (extract v_8656 8 16))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rax (concat (extract v_8652 0 48) v_8656);
      setRegister of v_8662;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8662;
      pure ()
    pat_end

def imull1 : instruction :=
  definst "imull" $ do
    pattern fun (v_2892 : reg (bv 32)) => do
      v_5039 <- getRegister v_2892;
      v_5042 <- getRegister rax;
      v_5046 <- eval (mul (mi 64 (svalueMInt v_5039)) (mi 64 (svalueMInt (extract v_5042 32 64))));
      v_5047 <- eval (extract v_5046 32 64);
      v_5052 <- eval (mux (notBool_ (eq v_5046 (mi 64 (svalueMInt v_5047)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister edx (extract v_5046 0 32);
      setRegister eax v_5047;
      setRegister of v_5052;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5052;
      pure ()
    pat_end;
    pattern fun (v_2905 : reg (bv 32)) (v_2906 : reg (bv 32)) => do
      v_5071 <- getRegister v_2906;
      v_5074 <- getRegister v_2905;
      v_5077 <- eval (mul (mi 64 (svalueMInt v_5071)) (mi 64 (svalueMInt v_5074)));
      v_5078 <- eval (extract v_5077 32 64);
      v_5083 <- eval (mux (notBool_ (eq v_5077 (mi 64 (svalueMInt v_5078)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2906) v_5078;
      setRegister of v_5083;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5083;
      pure ()
    pat_end;
    pattern fun (v_2912 : imm int) (v_2910 : reg (bv 32)) (v_2911 : reg (bv 32)) => do
      v_5091 <- getRegister v_2910;
      v_5097 <- eval (mul (mi 64 (svalueMInt v_5091)) (mi 64 (svalueMInt (handleImmediateWithSignExtend v_2912 32 32))));
      v_5098 <- eval (extract v_5097 32 64);
      v_5103 <- eval (mux (notBool_ (eq v_5097 (mi 64 (svalueMInt v_5098)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2911) v_5098;
      setRegister of v_5103;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5103;
      pure ()
    pat_end;
    pattern fun (v_2889 : Mem) => do
      v_8672 <- evaluateAddress v_2889;
      v_8673 <- load v_8672 4;
      v_8676 <- getRegister rax;
      v_8680 <- eval (mul (mi 64 (svalueMInt v_8673)) (mi 64 (svalueMInt (extract v_8676 32 64))));
      v_8681 <- eval (extract v_8680 32 64);
      v_8686 <- eval (mux (notBool_ (eq v_8680 (mi 64 (svalueMInt v_8681)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister edx (extract v_8680 0 32);
      setRegister eax v_8681;
      setRegister of v_8686;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8686;
      pure ()
    pat_end;
    pattern fun (v_2896 : Mem) (v_2897 : reg (bv 32)) => do
      v_8696 <- getRegister v_2897;
      v_8699 <- evaluateAddress v_2896;
      v_8700 <- load v_8699 4;
      v_8703 <- eval (mul (mi 64 (svalueMInt v_8696)) (mi 64 (svalueMInt v_8700)));
      v_8704 <- eval (extract v_8703 32 64);
      v_8709 <- eval (mux (notBool_ (eq v_8703 (mi 64 (svalueMInt v_8704)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2897) v_8704;
      setRegister of v_8709;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8709;
      pure ()
    pat_end;
    pattern fun (v_2902 : imm int) (v_2900 : Mem) (v_2901 : reg (bv 32)) => do
      v_8717 <- evaluateAddress v_2900;
      v_8718 <- load v_8717 4;
      v_8724 <- eval (mul (mi 64 (svalueMInt v_8718)) (mi 64 (svalueMInt (handleImmediateWithSignExtend v_2902 32 32))));
      v_8725 <- eval (extract v_8724 32 64);
      v_8730 <- eval (mux (notBool_ (eq v_8724 (mi 64 (svalueMInt v_8725)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2901) v_8725;
      setRegister of v_8730;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8730;
      pure ()
    pat_end

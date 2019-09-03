def imulw1 : instruction :=
  definst "imulw" $ do
    pattern fun (v_2946 : reg (bv 16)) => do
      v_5188 <- getRegister v_2946;
      v_5191 <- getRegister rax;
      v_5195 <- eval (mul (mi 32 (svalueMInt v_5188)) (mi 32 (svalueMInt (extract v_5191 48 64))));
      v_5196 <- eval (extract v_5195 16 32);
      v_5201 <- eval (mux (notBool_ (eq v_5195 (mi 32 (svalueMInt v_5196)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_5204 <- getRegister rdx;
      setRegister rdx (concat (extract v_5204 0 48) (extract v_5195 0 16));
      setRegister rax (concat (extract v_5191 0 48) v_5196);
      setRegister of v_5201;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5201;
      pure ()
    pat_end;
    pattern fun (v_2959 : reg (bv 16)) (v_2960 : reg (bv 16)) => do
      v_5225 <- getRegister v_2960;
      v_5228 <- getRegister v_2959;
      v_5231 <- eval (mul (mi 32 (svalueMInt v_5225)) (mi 32 (svalueMInt v_5228)));
      v_5232 <- eval (extract v_5231 16 32);
      v_5237 <- eval (mux (notBool_ (eq v_5231 (mi 32 (svalueMInt v_5232)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2960) v_5232;
      setRegister of v_5237;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5237;
      pure ()
    pat_end;
    pattern fun (v_2964 : imm int) (v_2965 : reg (bv 16)) (v_2966 : reg (bv 16)) => do
      v_5245 <- getRegister v_2965;
      v_5251 <- eval (mul (mi 32 (svalueMInt v_5245)) (mi 32 (svalueMInt (handleImmediateWithSignExtend v_2964 16 16))));
      v_5252 <- eval (extract v_5251 16 32);
      v_5257 <- eval (mux (notBool_ (eq v_5251 (mi 32 (svalueMInt v_5252)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2966) v_5252;
      setRegister of v_5257;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5257;
      pure ()
    pat_end;
    pattern fun (v_2943 : Mem) => do
      v_8803 <- evaluateAddress v_2943;
      v_8804 <- load v_8803 2;
      v_8807 <- getRegister rax;
      v_8811 <- eval (mul (mi 32 (svalueMInt v_8804)) (mi 32 (svalueMInt (extract v_8807 48 64))));
      v_8812 <- eval (extract v_8811 16 32);
      v_8817 <- eval (mux (notBool_ (eq v_8811 (mi 32 (svalueMInt v_8812)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      v_8820 <- getRegister rdx;
      setRegister rdx (concat (extract v_8820 0 48) (extract v_8811 0 16));
      setRegister rax (concat (extract v_8807 0 48) v_8812);
      setRegister of v_8817;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8817;
      pure ()
    pat_end;
    pattern fun (v_2950 : Mem) (v_2951 : reg (bv 16)) => do
      v_8832 <- getRegister v_2951;
      v_8835 <- evaluateAddress v_2950;
      v_8836 <- load v_8835 2;
      v_8839 <- eval (mul (mi 32 (svalueMInt v_8832)) (mi 32 (svalueMInt v_8836)));
      v_8840 <- eval (extract v_8839 16 32);
      v_8845 <- eval (mux (notBool_ (eq v_8839 (mi 32 (svalueMInt v_8840)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2951) v_8840;
      setRegister of v_8845;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8845;
      pure ()
    pat_end;
    pattern fun (v_2955 : imm int) (v_2954 : Mem) (v_2956 : reg (bv 16)) => do
      v_8853 <- evaluateAddress v_2954;
      v_8854 <- load v_8853 2;
      v_8860 <- eval (mul (mi 32 (svalueMInt v_8854)) (mi 32 (svalueMInt (handleImmediateWithSignExtend v_2955 16 16))));
      v_8861 <- eval (extract v_8860 16 32);
      v_8866 <- eval (mux (notBool_ (eq v_8860 (mi 32 (svalueMInt v_8861)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2956) v_8861;
      setRegister of v_8866;
      setRegister pf undef;
      setRegister af undef;
      setRegister zf undef;
      setRegister sf undef;
      setRegister cf v_8866;
      pure ()
    pat_end

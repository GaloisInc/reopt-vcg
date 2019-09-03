def imulq1 : instruction :=
  definst "imulq" $ do
    pattern fun (v_2919 : reg (bv 64)) => do
      v_5114 <- getRegister v_2919;
      v_5117 <- getRegister rax;
      v_5120 <- eval (mul (mi 128 (svalueMInt v_5114)) (mi 128 (svalueMInt v_5117)));
      v_5121 <- eval (extract v_5120 64 128);
      v_5126 <- eval (mux (notBool_ (eq v_5120 (mi 128 (svalueMInt v_5121)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rdx (extract v_5120 0 64);
      setRegister rax v_5121;
      setRegister of v_5126;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5126;
      pure ()
    pat_end;
    pattern fun (v_2932 : reg (bv 64)) (v_2933 : reg (bv 64)) => do
      v_5145 <- getRegister v_2933;
      v_5148 <- getRegister v_2932;
      v_5151 <- eval (mul (mi 128 (svalueMInt v_5145)) (mi 128 (svalueMInt v_5148)));
      v_5152 <- eval (extract v_5151 64 128);
      v_5157 <- eval (mux (notBool_ (eq v_5151 (mi 128 (svalueMInt v_5152)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2933) v_5152;
      setRegister of v_5157;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5157;
      pure ()
    pat_end;
    pattern fun (v_2939 : imm int) (v_2937 : reg (bv 64)) (v_2938 : reg (bv 64)) => do
      v_5165 <- getRegister v_2937;
      v_5171 <- eval (mul (mi 128 (svalueMInt v_5165)) (mi 128 (svalueMInt (handleImmediateWithSignExtend v_2939 32 32))));
      v_5172 <- eval (extract v_5171 64 128);
      v_5177 <- eval (mux (notBool_ (eq v_5171 (mi 128 (svalueMInt v_5172)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2938) v_5172;
      setRegister of v_5177;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_5177;
      pure ()
    pat_end;
    pattern fun (v_2916 : Mem) => do
      v_8738 <- evaluateAddress v_2916;
      v_8739 <- load v_8738 8;
      v_8742 <- getRegister rax;
      v_8745 <- eval (mul (mi 128 (svalueMInt v_8739)) (mi 128 (svalueMInt v_8742)));
      v_8746 <- eval (extract v_8745 64 128);
      v_8751 <- eval (mux (notBool_ (eq v_8745 (mi 128 (svalueMInt v_8746)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister rdx (extract v_8745 0 64);
      setRegister rax v_8746;
      setRegister of v_8751;
      setRegister zf undef;
      setRegister pf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8751;
      pure ()
    pat_end;
    pattern fun (v_2923 : Mem) (v_2924 : reg (bv 64)) => do
      v_8761 <- getRegister v_2924;
      v_8764 <- evaluateAddress v_2923;
      v_8765 <- load v_8764 8;
      v_8768 <- eval (mul (mi 128 (svalueMInt v_8761)) (mi 128 (svalueMInt v_8765)));
      v_8769 <- eval (extract v_8768 64 128);
      v_8774 <- eval (mux (notBool_ (eq v_8768 (mi 128 (svalueMInt v_8769)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2924) v_8769;
      setRegister of v_8774;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8774;
      pure ()
    pat_end;
    pattern fun (v_2929 : imm int) (v_2927 : Mem) (v_2928 : reg (bv 64)) => do
      v_8782 <- evaluateAddress v_2927;
      v_8783 <- load v_8782 8;
      v_8789 <- eval (mul (mi 128 (svalueMInt v_8783)) (mi 128 (svalueMInt (handleImmediateWithSignExtend v_2929 32 32))));
      v_8790 <- eval (extract v_8789 64 128);
      v_8795 <- eval (mux (notBool_ (eq v_8789 (mi 128 (svalueMInt v_8790)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister (lhs.of_reg v_2928) v_8790;
      setRegister of v_8795;
      setRegister pf undef;
      setRegister zf undef;
      setRegister af undef;
      setRegister sf undef;
      setRegister cf v_8795;
      pure ()
    pat_end

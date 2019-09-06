def mull1 : instruction :=
  definst "mull" $ do
    pattern fun (v_2808 : reg (bv 32)) => do
      v_4230 <- getRegister v_2808;
      v_4232 <- getRegister rax;
      v_4235 <- eval (mul (concat (expression.bv_nat 32 0) v_4230) (concat (expression.bv_nat 32 0) (extract v_4232 32 64)));
      v_4236 <- eval (extract v_4235 0 32);
      v_4238 <- eval (notBool_ (eq v_4236 (expression.bv_nat 32 0)));
      setRegister eax (extract v_4235 32 64);
      setRegister edx v_4236;
      setRegister af undef;
      setRegister cf v_4238;
      setRegister of v_4238;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2805 : Mem) => do
      v_8804 <- evaluateAddress v_2805;
      v_8805 <- load v_8804 4;
      v_8807 <- getRegister rax;
      v_8810 <- eval (mul (concat (expression.bv_nat 32 0) v_8805) (concat (expression.bv_nat 32 0) (extract v_8807 32 64)));
      v_8811 <- eval (extract v_8810 0 32);
      v_8813 <- eval (notBool_ (eq v_8811 (expression.bv_nat 32 0)));
      setRegister eax (extract v_8810 32 64);
      setRegister edx v_8811;
      setRegister af undef;
      setRegister cf v_8813;
      setRegister of v_8813;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end

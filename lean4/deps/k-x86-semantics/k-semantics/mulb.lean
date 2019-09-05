def mulb1 : instruction :=
  definst "mulb" $ do
    pattern fun (v_2775 : reg (bv 8)) => do
      v_4182 <- getRegister v_2775;
      v_4184 <- getRegister rax;
      v_4187 <- eval (mul (concat (expression.bv_nat 8 0) v_4182) (concat (expression.bv_nat 8 0) (extract v_4184 56 64)));
      v_4190 <- eval (notBool_ (eq (extract v_4187 0 8) (expression.bv_nat 8 0)));
      setRegister rax (concat (extract v_4184 0 48) v_4187);
      setRegister af undef;
      setRegister cf v_4190;
      setRegister of v_4190;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_2768 : Mem) => do
      v_8758 <- evaluateAddress v_2768;
      v_8759 <- load v_8758 1;
      v_8761 <- getRegister rax;
      v_8764 <- eval (mul (concat (expression.bv_nat 8 0) v_8759) (concat (expression.bv_nat 8 0) (extract v_8761 56 64)));
      v_8767 <- eval (notBool_ (eq (extract v_8764 0 8) (expression.bv_nat 8 0)));
      setRegister rax (concat (extract v_8761 0 48) v_8764);
      setRegister af undef;
      setRegister cf v_8767;
      setRegister of v_8767;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end

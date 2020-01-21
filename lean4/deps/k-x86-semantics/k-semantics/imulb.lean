def imulb : instruction :=
  definst "imulb" $ do
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 1;
      v_3 <- getRegister rax;
      v_4 <- eval (mul (sext v_2 16) (sext (extract v_3 56 64) 16));
      v_5 <- eval (notBool_ (eq v_4 (sext (extract v_4 8 16) 16)));
      setRegister rax (concat (extract v_3 0 48) v_4);
      setRegister af undef;
      setRegister cf v_5;
      setRegister of v_5;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (rh_0 : reg (bv 8)) => do
      v_1 <- getRegister (lhs.of_reg rh_0);
      v_2 <- getRegister rax;
      v_3 <- eval (mul (sext v_1 16) (sext (extract v_2 56 64) 16));
      v_4 <- eval (notBool_ (eq v_3 (sext (extract v_3 8 16) 16)));
      setRegister rax (concat (extract v_2 0 48) v_3);
      setRegister af undef;
      setRegister cf v_4;
      setRegister of v_4;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end

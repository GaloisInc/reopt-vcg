def imulw1 : instruction :=
  definst "imulw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (r16_2 : reg (bv 16)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 2;
      v_5 <- eval (mul (sext v_4 32) (sext (handleImmediateWithSignExtend imm_0 16 16) 32));
      v_6 <- eval (extract v_5 16 32);
      v_7 <- eval (notBool_ (eq v_5 (sext v_6 32)));
      setRegister (lhs.of_reg r16_2) v_6;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (imm_0 : imm int) (r16_1 : reg (bv 16)) (r16_2 : reg (bv 16)) => do
      v_3 <- getRegister r16_1;
      v_4 <- eval (mul (sext v_3 32) (sext (handleImmediateWithSignExtend imm_0 16 16) 32));
      v_5 <- eval (extract v_4 16 32);
      v_6 <- eval (notBool_ (eq v_4 (sext v_5 32)));
      setRegister (lhs.of_reg r16_2) v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister r16_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 2;
      v_5 <- eval (mul (sext v_2 32) (sext v_4 32));
      v_6 <- eval (extract v_5 16 32);
      v_7 <- eval (notBool_ (eq v_5 (sext v_6 32)));
      setRegister (lhs.of_reg r16_1) v_6;
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) => do
      v_1 <- evaluateAddress mem_0;
      v_2 <- load v_1 2;
      v_3 <- getRegister rax;
      v_4 <- eval (mul (sext v_2 32) (sext (extract v_3 48 64) 32));
      v_5 <- eval (extract v_4 16 32);
      v_6 <- eval (notBool_ (eq v_4 (sext v_5 32)));
      v_7 <- getRegister rdx;
      setRegister rax (concat (extract v_3 0 48) v_5);
      setRegister rdx (concat (extract v_7 0 48) (extract v_4 0 16));
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister r16_1;
      v_3 <- getRegister r16_0;
      v_4 <- eval (mul (sext v_2 32) (sext v_3 32));
      v_5 <- eval (extract v_4 16 32);
      v_6 <- eval (notBool_ (eq v_4 (sext v_5 32)));
      setRegister (lhs.of_reg r16_1) v_5;
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) => do
      v_1 <- getRegister r16_0;
      v_2 <- getRegister rax;
      v_3 <- eval (mul (sext v_1 32) (sext (extract v_2 48 64) 32));
      v_4 <- eval (extract v_3 16 32);
      v_5 <- eval (notBool_ (eq v_3 (sext v_4 32)));
      v_6 <- getRegister rdx;
      setRegister rax (concat (extract v_2 0 48) v_4);
      setRegister rdx (concat (extract v_6 0 48) (extract v_3 0 16));
      setRegister af undef;
      setRegister cf v_5;
      setRegister of v_5;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end

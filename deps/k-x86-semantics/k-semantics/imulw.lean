def imulw : instruction :=
  definst "imulw" $ do
    pattern fun (imm_0 : imm int) (mem_1 : Mem) (r16_2 : reg (bv 16)) => do
      v_3 <- evaluateAddress mem_1;
      v_4 <- load v_3 2;
      v_5 <- eval (mul (sext v_4 32) (sext (handleImmediateWithSignExtend imm_0 16 16) 32));
      (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
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
      v_3 <- getRegister (lhs.of_reg r16_1);
      v_4 <- eval (mul (sext v_3 32) (sext (handleImmediateWithSignExtend imm_0 16 16) 32));
      (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
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
      v_2 <- getRegister (lhs.of_reg r16_1);
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 2;
      v_5 <- eval (mul (sext v_2 32) (sext v_4 32));
      (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
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
      (v_4 : expression (bv 16)) <- eval (extract v_3 48 64);
      v_5 <- eval (mul (sext v_2 32) (sext v_4 32));
      (v_6 : expression (bv 16)) <- eval (extract v_5 16 32);
      v_7 <- eval (notBool_ (eq v_5 (sext v_6 32)));
      v_8 <- getRegister rdx;
      (v_9 : expression (bv 48)) <- eval (extract v_8 0 48);
      (v_10 : expression (bv 16)) <- eval (extract v_5 0 16);
      (v_11 : expression (bv 48)) <- eval (extract v_3 0 48);
      setRegister rax (concat v_11 v_6);
      setRegister rdx (concat v_9 v_10);
      setRegister af undef;
      setRegister cf v_7;
      setRegister of v_7;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (r16_0 : reg (bv 16)) (r16_1 : reg (bv 16)) => do
      v_2 <- getRegister (lhs.of_reg r16_1);
      v_3 <- getRegister (lhs.of_reg r16_0);
      v_4 <- eval (mul (sext v_2 32) (sext v_3 32));
      (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
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
      v_1 <- getRegister (lhs.of_reg r16_0);
      v_2 <- getRegister rax;
      (v_3 : expression (bv 16)) <- eval (extract v_2 48 64);
      v_4 <- eval (mul (sext v_1 32) (sext v_3 32));
      (v_5 : expression (bv 16)) <- eval (extract v_4 16 32);
      v_6 <- eval (notBool_ (eq v_4 (sext v_5 32)));
      v_7 <- getRegister rdx;
      (v_8 : expression (bv 48)) <- eval (extract v_7 0 48);
      (v_9 : expression (bv 16)) <- eval (extract v_4 0 16);
      (v_10 : expression (bv 48)) <- eval (extract v_2 0 48);
      setRegister rax (concat v_10 v_5);
      setRegister rdx (concat v_8 v_9);
      setRegister af undef;
      setRegister cf v_6;
      setRegister of v_6;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end

def imulw1 : instruction :=
  definst "imulw" $ do
    pattern fun (v_3037 : reg (bv 16)) => do
      v_5154 <- getRegister v_3037;
      v_5156 <- getRegister rax;
      v_5159 <- eval (mul (sext v_5154 32) (sext (extract v_5156 48 64) 32));
      v_5160 <- eval (extract v_5159 16 32);
      v_5163 <- eval (notBool_ (eq v_5159 (sext v_5160 32)));
      v_5164 <- getRegister rdx;
      setRegister rax (concat (extract v_5156 0 48) v_5160);
      setRegister rdx (concat (extract v_5164 0 48) (extract v_5159 0 16));
      setRegister af undef;
      setRegister cf v_5163;
      setRegister of v_5163;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3050 : reg (bv 16)) (v_3051 : reg (bv 16)) => do
      v_5187 <- getRegister v_3051;
      v_5189 <- getRegister v_3050;
      v_5191 <- eval (mul (sext v_5187 32) (sext v_5189 32));
      v_5192 <- eval (extract v_5191 16 32);
      v_5195 <- eval (notBool_ (eq v_5191 (sext v_5192 32)));
      setRegister (lhs.of_reg v_3051) v_5192;
      setRegister af undef;
      setRegister cf v_5195;
      setRegister of v_5195;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3055 : imm int) (v_3056 : reg (bv 16)) (v_3057 : reg (bv 16)) => do
      v_5203 <- getRegister v_3056;
      v_5207 <- eval (mul (sext v_5203 32) (sext (handleImmediateWithSignExtend v_3055 16 16) 32));
      v_5208 <- eval (extract v_5207 16 32);
      v_5211 <- eval (notBool_ (eq v_5207 (sext v_5208 32)));
      setRegister (lhs.of_reg v_3057) v_5208;
      setRegister af undef;
      setRegister cf v_5211;
      setRegister of v_5211;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3034 : Mem) => do
      v_8551 <- evaluateAddress v_3034;
      v_8552 <- load v_8551 2;
      v_8554 <- getRegister rax;
      v_8557 <- eval (mul (sext v_8552 32) (sext (extract v_8554 48 64) 32));
      v_8558 <- eval (extract v_8557 16 32);
      v_8561 <- eval (notBool_ (eq v_8557 (sext v_8558 32)));
      v_8562 <- getRegister rdx;
      setRegister rax (concat (extract v_8554 0 48) v_8558);
      setRegister rdx (concat (extract v_8562 0 48) (extract v_8557 0 16));
      setRegister af undef;
      setRegister cf v_8561;
      setRegister of v_8561;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3041 : Mem) (v_3042 : reg (bv 16)) => do
      v_8576 <- getRegister v_3042;
      v_8578 <- evaluateAddress v_3041;
      v_8579 <- load v_8578 2;
      v_8581 <- eval (mul (sext v_8576 32) (sext v_8579 32));
      v_8582 <- eval (extract v_8581 16 32);
      v_8585 <- eval (notBool_ (eq v_8581 (sext v_8582 32)));
      setRegister (lhs.of_reg v_3042) v_8582;
      setRegister af undef;
      setRegister cf v_8585;
      setRegister of v_8585;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3046 : imm int) (v_3045 : Mem) (v_3047 : reg (bv 16)) => do
      v_8593 <- evaluateAddress v_3045;
      v_8594 <- load v_8593 2;
      v_8598 <- eval (mul (sext v_8594 32) (sext (handleImmediateWithSignExtend v_3046 16 16) 32));
      v_8599 <- eval (extract v_8598 16 32);
      v_8602 <- eval (notBool_ (eq v_8598 (sext v_8599 32)));
      setRegister (lhs.of_reg v_3047) v_8599;
      setRegister af undef;
      setRegister cf v_8602;
      setRegister of v_8602;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end

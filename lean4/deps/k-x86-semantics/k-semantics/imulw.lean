def imulw1 : instruction :=
  definst "imulw" $ do
    pattern fun (v_3011 : reg (bv 16)) => do
      v_5133 <- getRegister v_3011;
      v_5135 <- getRegister rax;
      v_5138 <- eval (mul (sext v_5133 32) (sext (extract v_5135 48 64) 32));
      v_5139 <- eval (extract v_5138 16 32);
      v_5142 <- eval (notBool_ (eq v_5138 (sext v_5139 32)));
      v_5145 <- getRegister rdx;
      setRegister rdx (concat (extract v_5145 0 48) (extract v_5138 0 16));
      setRegister rax (concat (extract v_5135 0 48) v_5139);
      setRegister af undef;
      setRegister cf v_5142;
      setRegister of v_5142;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3024 : reg (bv 16)) (v_3025 : reg (bv 16)) => do
      v_5166 <- getRegister v_3025;
      v_5168 <- getRegister v_3024;
      v_5170 <- eval (mul (sext v_5166 32) (sext v_5168 32));
      v_5171 <- eval (extract v_5170 16 32);
      v_5174 <- eval (notBool_ (eq v_5170 (sext v_5171 32)));
      setRegister (lhs.of_reg v_3025) v_5171;
      setRegister af undef;
      setRegister cf v_5174;
      setRegister of v_5174;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3031 : imm int) (v_3029 : reg (bv 16)) (v_3030 : reg (bv 16)) => do
      v_5182 <- getRegister v_3029;
      v_5186 <- eval (mul (sext v_5182 32) (sext (handleImmediateWithSignExtend v_3031 16 16) 32));
      v_5187 <- eval (extract v_5186 16 32);
      v_5190 <- eval (notBool_ (eq v_5186 (sext v_5187 32)));
      setRegister (lhs.of_reg v_3030) v_5187;
      setRegister af undef;
      setRegister cf v_5190;
      setRegister of v_5190;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3007 : Mem) => do
      v_8541 <- evaluateAddress v_3007;
      v_8542 <- load v_8541 2;
      v_8544 <- getRegister rax;
      v_8547 <- eval (mul (sext v_8542 32) (sext (extract v_8544 48 64) 32));
      v_8548 <- eval (extract v_8547 16 32);
      v_8551 <- eval (notBool_ (eq v_8547 (sext v_8548 32)));
      v_8554 <- getRegister rdx;
      setRegister rdx (concat (extract v_8554 0 48) (extract v_8547 0 16));
      setRegister rax (concat (extract v_8544 0 48) v_8548);
      setRegister af undef;
      setRegister cf v_8551;
      setRegister of v_8551;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3014 : Mem) (v_3015 : reg (bv 16)) => do
      v_8566 <- getRegister v_3015;
      v_8568 <- evaluateAddress v_3014;
      v_8569 <- load v_8568 2;
      v_8571 <- eval (mul (sext v_8566 32) (sext v_8569 32));
      v_8572 <- eval (extract v_8571 16 32);
      v_8575 <- eval (notBool_ (eq v_8571 (sext v_8572 32)));
      setRegister (lhs.of_reg v_3015) v_8572;
      setRegister af undef;
      setRegister cf v_8575;
      setRegister of v_8575;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end;
    pattern fun (v_3020 : imm int) (v_3018 : Mem) (v_3019 : reg (bv 16)) => do
      v_8583 <- evaluateAddress v_3018;
      v_8584 <- load v_8583 2;
      v_8588 <- eval (mul (sext v_8584 32) (sext (handleImmediateWithSignExtend v_3020 16 16) 32));
      v_8589 <- eval (extract v_8588 16 32);
      v_8592 <- eval (notBool_ (eq v_8588 (sext v_8589 32)));
      setRegister (lhs.of_reg v_3019) v_8589;
      setRegister af undef;
      setRegister cf v_8592;
      setRegister of v_8592;
      setRegister pf undef;
      setRegister sf undef;
      setRegister zf undef;
      pure ()
    pat_end

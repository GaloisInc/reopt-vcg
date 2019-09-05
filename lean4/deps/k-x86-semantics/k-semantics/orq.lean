def orq1 : instruction :=
  definst "orq" $ do
    pattern fun (v_3062 : imm int) (v_3063 : reg (bv 64)) => do
      v_4835 <- getRegister v_3063;
      v_4836 <- eval (handleImmediateWithSignExtend v_3062 32 32);
      v_4838 <- eval (bv_or v_4835 (sext v_4836 64));
      setRegister (lhs.of_reg v_3063) v_4838;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4835 63 64) (extract v_4836 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4835 62 63) (extract v_4836 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4835 61 62) (extract v_4836 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4835 60 61) (extract v_4836 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4835 59 60) (extract v_4836 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4835 58 59) (extract v_4836 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4835 57 58) (extract v_4836 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4835 56 57) (extract v_4836 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_4838 0);
      setRegister zf (zeroFlag v_4838);
      pure ()
    pat_end;
    pattern fun (v_3071 : reg (bv 64)) (v_3072 : reg (bv 64)) => do
      v_4897 <- getRegister v_3072;
      v_4898 <- getRegister v_3071;
      v_4899 <- eval (bv_or v_4897 v_4898);
      setRegister (lhs.of_reg v_3072) v_4899;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_4899 56 64));
      setRegister sf (isBitSet v_4899 0);
      setRegister zf (zeroFlag v_4899);
      pure ()
    pat_end;
    pattern fun (v_3067 : Mem) (v_3068 : reg (bv 64)) => do
      v_8999 <- getRegister v_3068;
      v_9000 <- evaluateAddress v_3067;
      v_9001 <- load v_9000 8;
      v_9002 <- eval (bv_or v_8999 v_9001);
      setRegister (lhs.of_reg v_3068) v_9002;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_9002 56 64));
      setRegister sf (isBitSet v_9002 0);
      setRegister zf (zeroFlag v_9002);
      pure ()
    pat_end;
    pattern fun (v_3055 : imm int) (v_3054 : Mem) => do
      v_10876 <- evaluateAddress v_3054;
      v_10877 <- load v_10876 8;
      v_10878 <- eval (handleImmediateWithSignExtend v_3055 32 32);
      v_10880 <- eval (bv_or v_10877 (sext v_10878 64));
      store v_10876 v_10880 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_10877 63 64) (extract v_10878 31 32)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_10877 62 63) (extract v_10878 30 31)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10877 61 62) (extract v_10878 29 30)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10877 60 61) (extract v_10878 28 29)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10877 59 60) (extract v_10878 27 28)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10877 58 59) (extract v_10878 26 27)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10877 57 58) (extract v_10878 25 26)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_10877 56 57) (extract v_10878 24 25)) (expression.bv_nat 1 1)));
      setRegister sf (isBitSet v_10880 0);
      setRegister zf (zeroFlag v_10880);
      pure ()
    pat_end;
    pattern fun (v_3059 : reg (bv 64)) (v_3058 : Mem) => do
      v_10935 <- evaluateAddress v_3058;
      v_10936 <- load v_10935 8;
      v_10937 <- getRegister v_3059;
      v_10938 <- eval (bv_or v_10936 v_10937);
      store v_10935 v_10938 8;
      setRegister af undef;
      setRegister cf bit_zero;
      setRegister of bit_zero;
      setRegister pf (parityFlag (extract v_10938 56 64));
      setRegister sf (isBitSet v_10938 0);
      setRegister zf (zeroFlag v_10938);
      pure ()
    pat_end

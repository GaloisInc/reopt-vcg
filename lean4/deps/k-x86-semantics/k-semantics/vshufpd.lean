def vshufpd1 : instruction :=
  definst "vshufpd" $ do
    pattern fun (v_2906 : imm int) (v_2908 : reg (bv 128)) (v_2909 : reg (bv 128)) (v_2910 : reg (bv 128)) => do
      v_6937 <- eval (handleImmediateWithSignExtend v_2906 8 8);
      v_6940 <- getRegister v_2908;
      v_6946 <- getRegister v_2909;
      setRegister (lhs.of_reg v_2910) (concat (mux (eq (extract v_6937 6 7) (expression.bv_nat 1 1)) (extract v_6940 0 64) (extract v_6940 64 128)) (mux (eq (extract v_6937 7 8) (expression.bv_nat 1 1)) (extract v_6946 0 64) (extract v_6946 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2919 : imm int) (v_2920 : reg (bv 256)) (v_2921 : reg (bv 256)) (v_2922 : reg (bv 256)) => do
      v_6958 <- eval (handleImmediateWithSignExtend v_2919 8 8);
      v_6961 <- getRegister v_2920;
      v_6967 <- getRegister v_2921;
      setRegister (lhs.of_reg v_2922) (concat (mux (eq (extract v_6958 4 5) (expression.bv_nat 1 1)) (extract v_6961 0 64) (extract v_6961 64 128)) (concat (mux (eq (extract v_6958 5 6) (expression.bv_nat 1 1)) (extract v_6967 0 64) (extract v_6967 64 128)) (concat (mux (eq (extract v_6958 6 7) (expression.bv_nat 1 1)) (extract v_6961 128 192) (extract v_6961 192 256)) (mux (eq (extract v_6958 7 8) (expression.bv_nat 1 1)) (extract v_6967 128 192) (extract v_6967 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_2900 : imm int) (v_2901 : Mem) (v_2902 : reg (bv 128)) (v_2903 : reg (bv 128)) => do
      v_13145 <- eval (handleImmediateWithSignExtend v_2900 8 8);
      v_13148 <- evaluateAddress v_2901;
      v_13149 <- load v_13148 16;
      v_13155 <- getRegister v_2902;
      setRegister (lhs.of_reg v_2903) (concat (mux (eq (extract v_13145 6 7) (expression.bv_nat 1 1)) (extract v_13149 0 64) (extract v_13149 64 128)) (mux (eq (extract v_13145 7 8) (expression.bv_nat 1 1)) (extract v_13155 0 64) (extract v_13155 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2913 : imm int) (v_2914 : Mem) (v_2915 : reg (bv 256)) (v_2916 : reg (bv 256)) => do
      v_13161 <- eval (handleImmediateWithSignExtend v_2913 8 8);
      v_13164 <- evaluateAddress v_2914;
      v_13165 <- load v_13164 32;
      v_13171 <- getRegister v_2915;
      setRegister (lhs.of_reg v_2916) (concat (mux (eq (extract v_13161 4 5) (expression.bv_nat 1 1)) (extract v_13165 0 64) (extract v_13165 64 128)) (concat (mux (eq (extract v_13161 5 6) (expression.bv_nat 1 1)) (extract v_13171 0 64) (extract v_13171 64 128)) (concat (mux (eq (extract v_13161 6 7) (expression.bv_nat 1 1)) (extract v_13165 128 192) (extract v_13165 192 256)) (mux (eq (extract v_13161 7 8) (expression.bv_nat 1 1)) (extract v_13171 128 192) (extract v_13171 192 256)))));
      pure ()
    pat_end

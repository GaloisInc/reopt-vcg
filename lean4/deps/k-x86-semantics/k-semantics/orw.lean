def orw1 : instruction :=
  definst "orw" $ do
    pattern fun (v_3018 : imm int) ax => do
      v_4968 <- getRegister rax;
      v_4970 <- eval (handleImmediateWithSignExtend v_3018 16 16);
      v_4974 <- eval (bv_or (extract v_4968 48 64) v_4970);
      setRegister rax (concat (extract v_4968 0 48) v_4974);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_4968 63 64) (extract v_4970 15 16)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_4968 62 63) (extract v_4970 14 15)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4968 61 62) (extract v_4970 13 14)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4968 60 61) (extract v_4970 12 13)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4968 59 60) (extract v_4970 11 12)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4968 58 59) (extract v_4970 10 11)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4968 57 58) (extract v_4970 9 10)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_4968 56 57) (extract v_4970 8 9)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_4974);
      setRegister af undef;
      setRegister sf (bv_or (extract v_4968 48 49) (extract v_4970 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3030 : imm int) (v_3031 : reg (bv 16)) => do
      v_5039 <- getRegister v_3031;
      v_5041 <- eval (bv_or v_5039 (handleImmediateWithSignExtend v_3030 16 16));
      setRegister (lhs.of_reg v_3031) v_5041;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5041 8 16));
      setRegister zf (zeroFlag v_5041);
      setRegister af undef;
      setRegister sf (extract v_5041 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3039 : reg (bv 16)) (v_3040 : reg (bv 16)) => do
      v_5057 <- getRegister v_3040;
      v_5058 <- getRegister v_3039;
      v_5059 <- eval (bv_or v_5057 v_5058);
      setRegister (lhs.of_reg v_3040) v_5059;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5059 8 16));
      setRegister zf (zeroFlag v_5059);
      setRegister af undef;
      setRegister sf (extract v_5059 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3034 : Mem) (v_3035 : reg (bv 16)) => do
      v_9177 <- getRegister v_3035;
      v_9178 <- evaluateAddress v_3034;
      v_9179 <- load v_9178 2;
      v_9180 <- eval (bv_or v_9177 v_9179);
      setRegister (lhs.of_reg v_3035) v_9180;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9180 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_9180);
      setRegister sf (extract v_9180 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3022 : imm int) (v_3021 : Mem) => do
      v_11313 <- evaluateAddress v_3021;
      v_11314 <- load v_11313 2;
      v_11316 <- eval (bv_or v_11314 (handleImmediateWithSignExtend v_3022 16 16));
      store v_11313 v_11316 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11316 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_11316);
      setRegister sf (extract v_11316 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3026 : reg (bv 16)) (v_3025 : Mem) => do
      v_11328 <- evaluateAddress v_3025;
      v_11329 <- load v_11328 2;
      v_11330 <- getRegister v_3026;
      v_11331 <- eval (bv_or v_11329 v_11330);
      store v_11328 v_11331 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11331 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_11331);
      setRegister sf (extract v_11331 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end

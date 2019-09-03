def orw1 : instruction :=
  definst "orw" $ do
    pattern fun (v_3030 : imm int) ax => do
      v_5055 <- getRegister rax;
      v_5057 <- eval (handleImmediateWithSignExtend v_3030 16 16);
      v_5061 <- eval (bv_or (extract v_5055 48 64) v_5057);
      setRegister rax (concat (extract v_5055 0 48) v_5061);
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (mux (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (bv_or (extract v_5055 63 64) (extract v_5057 15 16)) (expression.bv_nat 1 1)) (eq (bv_or (extract v_5055 62 63) (extract v_5057 14 15)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_5055 61 62) (extract v_5057 13 14)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_5055 60 61) (extract v_5057 12 13)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_5055 59 60) (extract v_5057 11 12)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_5055 58 59) (extract v_5057 10 11)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_5055 57 58) (extract v_5057 9 10)) (expression.bv_nat 1 1)))) (eq (bv_or (extract v_5055 56 57) (extract v_5057 8 9)) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (zeroFlag v_5061);
      setRegister af undef;
      setRegister sf (bv_or (extract v_5055 48 49) (extract v_5057 0 1));
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3043 : imm int) (v_3042 : reg (bv 16)) => do
      v_5126 <- getRegister v_3042;
      v_5128 <- eval (bv_or v_5126 (handleImmediateWithSignExtend v_3043 16 16));
      setRegister (lhs.of_reg v_3042) v_5128;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5128 8 16));
      setRegister zf (zeroFlag v_5128);
      setRegister af undef;
      setRegister sf (extract v_5128 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3051 : reg (bv 16)) (v_3052 : reg (bv 16)) => do
      v_5144 <- getRegister v_3052;
      v_5145 <- getRegister v_3051;
      v_5146 <- eval (bv_or v_5144 v_5145);
      setRegister (lhs.of_reg v_3052) v_5146;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_5146 8 16));
      setRegister zf (zeroFlag v_5146);
      setRegister af undef;
      setRegister sf (extract v_5146 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3047 : Mem) (v_3048 : reg (bv 16)) => do
      v_9252 <- getRegister v_3048;
      v_9253 <- evaluateAddress v_3047;
      v_9254 <- load v_9253 2;
      v_9255 <- eval (bv_or v_9252 v_9254);
      setRegister (lhs.of_reg v_3048) v_9255;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_9255 8 16));
      setRegister zf (zeroFlag v_9255);
      setRegister af undef;
      setRegister sf (extract v_9255 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3035 : imm int) (v_3034 : Mem) => do
      v_11264 <- evaluateAddress v_3034;
      v_11265 <- load v_11264 2;
      v_11267 <- eval (bv_or v_11265 (handleImmediateWithSignExtend v_3035 16 16));
      store v_11264 v_11267 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11267 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_11267);
      setRegister sf (extract v_11267 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end;
    pattern fun (v_3039 : reg (bv 16)) (v_3038 : Mem) => do
      v_11279 <- evaluateAddress v_3038;
      v_11280 <- load v_11279 2;
      v_11281 <- getRegister v_3039;
      v_11282 <- eval (bv_or v_11280 v_11281);
      store v_11279 v_11282 2;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (parityFlag (extract v_11282 8 16));
      setRegister af undef;
      setRegister zf (zeroFlag v_11282);
      setRegister sf (extract v_11282 0 1);
      setRegister cf (expression.bv_nat 1 0);
      pure ()
    pat_end

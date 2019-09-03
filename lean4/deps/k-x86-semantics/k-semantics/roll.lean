def roll1 : instruction :=
  definst "roll" $ do
    pattern fun cl (v_2610 : reg (bv 32)) => do
      v_4993 <- getRegister rcx;
      v_4995 <- eval (bv_and (extract v_4993 56 64) (expression.bv_nat 8 31));
      v_4996 <- eval (eq v_4995 (expression.bv_nat 8 0));
      v_4997 <- eval (notBool_ v_4996);
      v_4998 <- getRegister v_2610;
      v_5001 <- eval (rolHelper v_4998 (uvalueMInt (concat (expression.bv_nat 24 0) v_4995)) 0);
      v_5003 <- eval (eq (extract v_5001 31 32) (expression.bv_nat 1 1));
      v_5005 <- getRegister cf;
      v_5010 <- eval (eq v_4995 (expression.bv_nat 8 1));
      v_5018 <- getRegister of;
      setRegister (lhs.of_reg v_2610) v_5001;
      setRegister of (mux (bit_or (bit_and v_5010 (notBool_ (eq (eq (extract v_5001 0 1) (expression.bv_nat 1 1)) v_5003))) (bit_and (notBool_ v_5010) (bit_or (bit_and v_4997 undef) (bit_and v_4996 (eq v_5018 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_4997 v_5003) (bit_and v_4996 (eq v_5005 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2613 : imm int) (v_2615 : reg (bv 32)) => do
      v_5029 <- eval (bv_and (handleImmediateWithSignExtend v_2613 8 8) (expression.bv_nat 8 31));
      v_5030 <- eval (eq v_5029 (expression.bv_nat 8 0));
      v_5031 <- eval (notBool_ v_5030);
      v_5032 <- getRegister v_2615;
      v_5035 <- eval (rolHelper v_5032 (uvalueMInt (concat (expression.bv_nat 24 0) v_5029)) 0);
      v_5037 <- eval (eq (extract v_5035 31 32) (expression.bv_nat 1 1));
      v_5039 <- getRegister cf;
      v_5044 <- eval (eq v_5029 (expression.bv_nat 8 1));
      v_5052 <- getRegister of;
      setRegister (lhs.of_reg v_2615) v_5035;
      setRegister of (mux (bit_or (bit_and v_5044 (notBool_ (eq (eq (extract v_5035 0 1) (expression.bv_nat 1 1)) v_5037))) (bit_and (notBool_ v_5044) (bit_or (bit_and v_5031 undef) (bit_and v_5030 (eq v_5052 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5031 v_5037) (bit_and v_5030 (eq v_5039 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2619 : reg (bv 32)) => do
      v_5062 <- getRegister v_2619;
      v_5067 <- eval (add (extract (shl v_5062 1) 0 32) (concat (expression.bv_nat 31 0) (extract v_5062 0 1)));
      v_5068 <- eval (extract v_5067 31 32);
      setRegister (lhs.of_reg v_2619) v_5067;
      setRegister of (mux (notBool_ (eq (eq (extract v_5067 0 1) (expression.bv_nat 1 1)) (eq v_5068 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5068;
      pure ()
    pat_end;
    pattern fun cl (v_2596 : Mem) => do
      v_14230 <- evaluateAddress v_2596;
      v_14231 <- load v_14230 4;
      v_14232 <- getRegister rcx;
      v_14234 <- eval (bv_and (extract v_14232 56 64) (expression.bv_nat 8 31));
      v_14237 <- eval (rolHelper v_14231 (uvalueMInt (concat (expression.bv_nat 24 0) v_14234)) 0);
      store v_14230 v_14237 4;
      v_14239 <- eval (eq v_14234 (expression.bv_nat 8 0));
      v_14240 <- eval (notBool_ v_14239);
      v_14242 <- eval (eq (extract v_14237 31 32) (expression.bv_nat 1 1));
      v_14244 <- getRegister cf;
      v_14249 <- eval (eq v_14234 (expression.bv_nat 8 1));
      v_14257 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14249 (notBool_ (eq (eq (extract v_14237 0 1) (expression.bv_nat 1 1)) v_14242))) (bit_and (notBool_ v_14249) (bit_or (bit_and v_14240 undef) (bit_and v_14239 (eq v_14257 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14240 v_14242) (bit_and v_14239 (eq v_14244 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2600 : imm int) (v_2599 : Mem) => do
      v_14266 <- evaluateAddress v_2599;
      v_14267 <- load v_14266 4;
      v_14269 <- eval (bv_and (handleImmediateWithSignExtend v_2600 8 8) (expression.bv_nat 8 31));
      v_14272 <- eval (rolHelper v_14267 (uvalueMInt (concat (expression.bv_nat 24 0) v_14269)) 0);
      store v_14266 v_14272 4;
      v_14274 <- eval (eq v_14269 (expression.bv_nat 8 0));
      v_14275 <- eval (notBool_ v_14274);
      v_14277 <- eval (eq (extract v_14272 31 32) (expression.bv_nat 1 1));
      v_14279 <- getRegister cf;
      v_14284 <- eval (eq v_14269 (expression.bv_nat 8 1));
      v_14292 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14284 (notBool_ (eq (eq (extract v_14272 0 1) (expression.bv_nat 1 1)) v_14277))) (bit_and (notBool_ v_14284) (bit_or (bit_and v_14275 undef) (bit_and v_14274 (eq v_14292 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14275 v_14277) (bit_and v_14274 (eq v_14279 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2603 : Mem) => do
      v_17886 <- evaluateAddress v_2603;
      v_17887 <- load v_17886 4;
      v_17892 <- eval (add (extract (shl v_17887 1) 0 32) (concat (expression.bv_nat 31 0) (extract v_17887 0 1)));
      store v_17886 v_17892 4;
      v_17895 <- eval (eq (extract v_17892 31 32) (expression.bv_nat 1 1));
      setRegister of (mux (notBool_ (eq (eq (extract v_17892 0 1) (expression.bv_nat 1 1)) v_17895)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux v_17895 (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2603 : Mem) => do
      v_17904 <- evaluateAddress v_2603;
      v_17905 <- load v_17904 4;
      v_17910 <- eval (add (extract (shl v_17905 1) 0 32) (concat (expression.bv_nat 31 0) (extract v_17905 0 1)));
      store v_17904 v_17910 4;
      v_17912 <- eval (extract v_17910 31 32);
      setRegister of (mux (notBool_ (eq (eq (extract v_17910 0 1) (expression.bv_nat 1 1)) (eq v_17912 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_17912;
      pure ()
    pat_end

def subl1 : instruction :=
  definst "subl" $ do
    pattern fun (v_3161 : imm int) eax => do
      v_7055 <- eval (handleImmediateWithSignExtend v_3161 32 32);
      v_7059 <- getRegister rax;
      v_7062 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7055 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) (extract v_7059 32 64)));
      v_7067 <- eval (extract v_7062 1 2);
      v_7073 <- eval (extract v_7062 1 33);
      v_7079 <- eval (eq (bv_xor (extract v_7055 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister eax v_7073;
      setRegister of (mux (bit_and (eq v_7079 (eq (extract v_7059 32 33) (expression.bv_nat 1 1))) (notBool_ (eq v_7079 (eq v_7067 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7062 25 33));
      setRegister zf (zeroFlag v_7073);
      setRegister af (bv_xor (bv_xor (extract v_7055 27 28) (extract v_7059 59 60)) (extract v_7062 28 29));
      setRegister sf v_7067;
      setRegister cf (mux (notBool_ (eq (extract v_7062 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3173 : imm int) (v_3175 : reg (bv 32)) => do
      v_7103 <- eval (handleImmediateWithSignExtend v_3173 32 32);
      v_7107 <- getRegister v_3175;
      v_7109 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7103 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_7107));
      v_7114 <- eval (extract v_7109 1 2);
      v_7119 <- eval (extract v_7109 1 33);
      v_7125 <- eval (eq (bv_xor (extract v_7103 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3175) v_7119;
      setRegister of (mux (bit_and (eq v_7125 (eq (extract v_7107 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7125 (eq v_7114 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7109 25 33));
      setRegister zf (zeroFlag v_7119);
      setRegister af (bv_xor (extract (bv_xor v_7103 v_7107) 27 28) (extract v_7109 28 29));
      setRegister sf v_7114;
      setRegister cf (mux (notBool_ (eq (extract v_7109 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3183 : reg (bv 32)) (v_3184 : reg (bv 32)) => do
      v_7145 <- getRegister v_3183;
      v_7149 <- getRegister v_3184;
      v_7151 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7145 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_7149));
      v_7156 <- eval (extract v_7151 1 2);
      v_7161 <- eval (extract v_7151 1 33);
      v_7167 <- eval (eq (bv_xor (extract v_7145 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3184) v_7161;
      setRegister of (mux (bit_and (eq v_7167 (eq (extract v_7149 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7167 (eq v_7156 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7151 25 33));
      setRegister zf (zeroFlag v_7161);
      setRegister af (bv_xor (extract (bv_xor v_7145 v_7149) 27 28) (extract v_7151 28 29));
      setRegister sf v_7156;
      setRegister cf (mux (notBool_ (eq (extract v_7151 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3178 : Mem) (v_3179 : reg (bv 32)) => do
      v_10388 <- evaluateAddress v_3178;
      v_10389 <- load v_10388 4;
      v_10393 <- getRegister v_3179;
      v_10395 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10389 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_10393));
      v_10400 <- eval (extract v_10395 1 2);
      v_10405 <- eval (extract v_10395 1 33);
      v_10411 <- eval (eq (bv_xor (extract v_10389 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3179) v_10405;
      setRegister of (mux (bit_and (eq v_10411 (eq (extract v_10393 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10411 (eq v_10400 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10395 25 33));
      setRegister zf (zeroFlag v_10405);
      setRegister af (bv_xor (extract (bv_xor v_10389 v_10393) 27 28) (extract v_10395 28 29));
      setRegister sf v_10400;
      setRegister cf (mux (notBool_ (eq (extract v_10395 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3165 : imm int) (v_3166 : Mem) => do
      v_13135 <- evaluateAddress v_3166;
      v_13136 <- eval (handleImmediateWithSignExtend v_3165 32 32);
      v_13140 <- load v_13135 4;
      v_13142 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13136 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_13140));
      v_13143 <- eval (extract v_13142 1 33);
      store v_13135 v_13143 4;
      v_13149 <- eval (extract v_13142 1 2);
      v_13159 <- eval (eq (bv_xor (extract v_13136 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13159 (eq (extract v_13140 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13159 (eq v_13149 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13142 25 33));
      setRegister af (bv_xor (extract (bv_xor v_13136 v_13140) 27 28) (extract v_13142 28 29));
      setRegister zf (zeroFlag v_13143);
      setRegister sf v_13149;
      setRegister cf (mux (notBool_ (eq (extract v_13142 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3170 : reg (bv 32)) (v_3169 : Mem) => do
      v_13174 <- evaluateAddress v_3169;
      v_13175 <- getRegister v_3170;
      v_13179 <- load v_13174 4;
      v_13181 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13175 (expression.bv_nat 32 4294967295))) (expression.bv_nat 33 1)) (concat (expression.bv_nat 1 0) v_13179));
      v_13182 <- eval (extract v_13181 1 33);
      store v_13174 v_13182 4;
      v_13188 <- eval (extract v_13181 1 2);
      v_13198 <- eval (eq (bv_xor (extract v_13175 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13198 (eq (extract v_13179 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13198 (eq v_13188 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13181 25 33));
      setRegister af (bv_xor (extract (bv_xor v_13175 v_13179) 27 28) (extract v_13181 28 29));
      setRegister zf (zeroFlag v_13182);
      setRegister sf v_13188;
      setRegister cf (mux (notBool_ (eq (extract v_13181 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

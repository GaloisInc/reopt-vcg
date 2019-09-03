def sbbb1 : instruction :=
  definst "sbbb" $ do
    pattern fun (v_3183 : imm int) al => do
      v_8159 <- getRegister cf;
      v_8161 <- eval (handleImmediateWithSignExtend v_3183 8 8);
      v_8163 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8161 (expression.bv_nat 8 255)));
      v_8166 <- getRegister rax;
      v_8169 <- eval (add (mux (eq v_8159 (expression.bv_nat 1 1)) v_8163 (add v_8163 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) (extract v_8166 56 64)));
      v_8174 <- eval (extract v_8169 1 2);
      v_8180 <- eval (extract v_8169 1 9);
      v_8185 <- eval (eq (bv_xor (extract v_8161 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_8166 0 56) v_8180);
      setRegister of (mux (bit_and (eq v_8185 (eq (extract v_8166 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_8185 (eq v_8174 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8180);
      setRegister zf (zeroFlag v_8180);
      setRegister af (bv_xor (bv_xor (extract v_8161 3 4) (extract v_8166 59 60)) (extract v_8169 4 5));
      setRegister sf v_8174;
      setRegister cf (mux (notBool_ (eq (extract v_8169 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3199 : imm int) (v_3201 : reg (bv 8)) => do
      v_8215 <- getRegister cf;
      v_8217 <- eval (handleImmediateWithSignExtend v_3199 8 8);
      v_8219 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8217 (expression.bv_nat 8 255)));
      v_8222 <- getRegister v_3201;
      v_8224 <- eval (add (mux (eq v_8215 (expression.bv_nat 1 1)) v_8219 (add v_8219 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_8222));
      v_8229 <- eval (extract v_8224 1 2);
      v_8230 <- eval (extract v_8224 1 9);
      v_8239 <- eval (eq (bv_xor (extract v_8217 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3201) v_8230;
      setRegister of (mux (bit_and (eq v_8239 (eq (extract v_8222 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8239 (eq v_8229 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8230);
      setRegister af (bv_xor (extract (bv_xor v_8217 v_8222) 3 4) (extract v_8224 4 5));
      setRegister zf (zeroFlag v_8230);
      setRegister sf v_8229;
      setRegister cf (mux (notBool_ (eq (extract v_8224 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3209 : reg (bv 8)) (v_3210 : reg (bv 8)) => do
      v_8259 <- getRegister cf;
      v_8261 <- getRegister v_3209;
      v_8263 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8261 (expression.bv_nat 8 255)));
      v_8266 <- getRegister v_3210;
      v_8268 <- eval (add (mux (eq v_8259 (expression.bv_nat 1 1)) v_8263 (add v_8263 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_8266));
      v_8273 <- eval (extract v_8268 1 2);
      v_8274 <- eval (extract v_8268 1 9);
      v_8283 <- eval (eq (bv_xor (extract v_8261 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3210) v_8274;
      setRegister of (mux (bit_and (eq v_8283 (eq (extract v_8266 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8283 (eq v_8273 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8274);
      setRegister af (bv_xor (extract (bv_xor v_8261 v_8266) 3 4) (extract v_8268 4 5));
      setRegister zf (zeroFlag v_8274);
      setRegister sf v_8273;
      setRegister cf (mux (notBool_ (eq (extract v_8268 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3204 : Mem) (v_3205 : reg (bv 8)) => do
      v_13119 <- getRegister cf;
      v_13121 <- evaluateAddress v_3204;
      v_13122 <- load v_13121 1;
      v_13124 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13122 (expression.bv_nat 8 255)));
      v_13127 <- getRegister v_3205;
      v_13129 <- eval (add (mux (eq v_13119 (expression.bv_nat 1 1)) v_13124 (add v_13124 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_13127));
      v_13134 <- eval (extract v_13129 1 2);
      v_13139 <- eval (extract v_13129 1 9);
      v_13144 <- eval (eq (bv_xor (extract v_13122 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3205) v_13139;
      setRegister of (mux (bit_and (eq v_13144 (eq (extract v_13127 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13144 (eq v_13134 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13139);
      setRegister zf (zeroFlag v_13139);
      setRegister af (bv_xor (extract (bv_xor v_13122 v_13127) 3 4) (extract v_13129 4 5));
      setRegister sf v_13134;
      setRegister cf (mux (notBool_ (eq (extract v_13129 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3223 : Mem) (v_3224 : reg (bv 8)) => do
      v_13160 <- getRegister cf;
      v_13162 <- evaluateAddress v_3223;
      v_13163 <- load v_13162 1;
      v_13165 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13163 (expression.bv_nat 8 255)));
      v_13168 <- getRegister v_3224;
      v_13170 <- eval (add (mux (eq v_13160 (expression.bv_nat 1 1)) v_13165 (add v_13165 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_13168));
      v_13175 <- eval (extract v_13170 1 2);
      v_13176 <- eval (extract v_13170 1 9);
      v_13185 <- eval (eq (bv_xor (extract v_13163 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3224) v_13176;
      setRegister of (mux (bit_and (eq v_13185 (eq (extract v_13168 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13185 (eq v_13175 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13176);
      setRegister af (bv_xor (extract (bv_xor v_13163 v_13168) 3 4) (extract v_13170 4 5));
      setRegister zf (zeroFlag v_13176);
      setRegister sf v_13175;
      setRegister cf (mux (notBool_ (eq (extract v_13170 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3188 : imm int) (v_3187 : Mem) => do
      v_17509 <- evaluateAddress v_3187;
      v_17510 <- getRegister cf;
      v_17512 <- eval (handleImmediateWithSignExtend v_3188 8 8);
      v_17514 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17512 (expression.bv_nat 8 255)));
      v_17517 <- load v_17509 1;
      v_17519 <- eval (add (mux (eq v_17510 (expression.bv_nat 1 1)) v_17514 (add v_17514 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_17517));
      v_17520 <- eval (extract v_17519 1 9);
      store v_17509 v_17520 1;
      v_17526 <- eval (extract v_17519 1 2);
      v_17535 <- eval (eq (bv_xor (extract v_17512 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17535 (eq (extract v_17517 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17535 (eq v_17526 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_17520);
      setRegister af (bv_xor (extract (bv_xor v_17512 v_17517) 3 4) (extract v_17519 4 5));
      setRegister zf (zeroFlag v_17520);
      setRegister sf v_17526;
      setRegister cf (mux (notBool_ (eq (extract v_17519 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3192 : reg (bv 8)) (v_3191 : Mem) => do
      v_17550 <- evaluateAddress v_3191;
      v_17551 <- getRegister cf;
      v_17553 <- getRegister v_3192;
      v_17555 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17553 (expression.bv_nat 8 255)));
      v_17558 <- load v_17550 1;
      v_17560 <- eval (add (mux (eq v_17551 (expression.bv_nat 1 1)) v_17555 (add v_17555 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_17558));
      v_17561 <- eval (extract v_17560 1 9);
      store v_17550 v_17561 1;
      v_17567 <- eval (extract v_17560 1 2);
      v_17576 <- eval (eq (bv_xor (extract v_17553 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17576 (eq (extract v_17558 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17576 (eq v_17567 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_17561);
      setRegister af (bv_xor (extract (bv_xor v_17553 v_17558) 3 4) (extract v_17560 4 5));
      setRegister zf (zeroFlag v_17561);
      setRegister sf v_17567;
      setRegister cf (mux (notBool_ (eq (extract v_17560 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

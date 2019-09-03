def subq1 : instruction :=
  definst "subq" $ do
    pattern fun (v_3200 : imm int) (v_3202 : reg (bv 64)) => do
      v_7289 <- eval (handleImmediateWithSignExtend v_3200 32 32);
      v_7291 <- eval (mi 64 (svalueMInt v_7289));
      v_7297 <- getRegister v_3202;
      v_7299 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7291 (mi (bitwidthMInt v_7291) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7297));
      v_7304 <- eval (extract v_7299 1 2);
      v_7305 <- eval (extract v_7299 1 65);
      v_7314 <- eval (extract v_7291 0 1);
      v_7318 <- eval (eq (bv_xor v_7314 (mi (bitwidthMInt v_7314) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3202) v_7305;
      setRegister of (mux (bit_and (eq v_7318 (eq (extract v_7297 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7318 (eq v_7304 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7299 57 65));
      setRegister af (bv_xor (bv_xor (extract v_7289 27 28) (extract v_7297 59 60)) (extract v_7299 60 61));
      setRegister zf (zeroFlag v_7305);
      setRegister sf v_7304;
      setRegister cf (mux (notBool_ (eq (extract v_7299 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3210 : reg (bv 64)) (v_3211 : reg (bv 64)) => do
      v_7338 <- getRegister v_3210;
      v_7344 <- getRegister v_3211;
      v_7346 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7338 (mi (bitwidthMInt v_7338) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7344));
      v_7351 <- eval (extract v_7346 1 2);
      v_7352 <- eval (extract v_7346 1 65);
      v_7360 <- eval (extract v_7338 0 1);
      v_7364 <- eval (eq (bv_xor v_7360 (mi (bitwidthMInt v_7360) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3211) v_7352;
      setRegister of (mux (bit_and (eq v_7364 (eq (extract v_7344 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7364 (eq v_7351 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7346 57 65));
      setRegister af (bv_xor (extract (bv_xor v_7338 v_7344) 59 60) (extract v_7346 60 61));
      setRegister zf (zeroFlag v_7352);
      setRegister sf v_7351;
      setRegister cf (mux (notBool_ (eq (extract v_7346 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3214 : imm int) rax => do
      v_7380 <- eval (handleImmediateWithSignExtend v_3214 32 32);
      v_7382 <- eval (mi 64 (svalueMInt v_7380));
      v_7388 <- getRegister rax;
      v_7390 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7382 (mi (bitwidthMInt v_7382) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7388));
      v_7395 <- eval (extract v_7390 1 2);
      v_7401 <- eval (extract v_7390 1 65);
      v_7405 <- eval (extract v_7382 0 1);
      v_7409 <- eval (eq (bv_xor v_7405 (mi (bitwidthMInt v_7405) -1)) (expression.bv_nat 1 1));
      setRegister rax v_7401;
      setRegister of (mux (bit_and (eq v_7409 (eq (extract v_7388 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7409 (eq v_7395 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7390 57 65));
      setRegister zf (zeroFlag v_7401);
      setRegister af (bv_xor (bv_xor (extract v_7380 27 28) (extract v_7388 59 60)) (extract v_7390 60 61));
      setRegister sf v_7395;
      setRegister cf (mux (notBool_ (eq (extract v_7390 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3205 : Mem) (v_3206 : reg (bv 64)) => do
      v_10467 <- evaluateAddress v_3205;
      v_10468 <- load v_10467 8;
      v_10474 <- getRegister v_3206;
      v_10476 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10468 (mi (bitwidthMInt v_10468) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_10474));
      v_10481 <- eval (extract v_10476 1 2);
      v_10482 <- eval (extract v_10476 1 65);
      v_10490 <- eval (extract v_10468 0 1);
      v_10494 <- eval (eq (bv_xor v_10490 (mi (bitwidthMInt v_10490) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3206) v_10482;
      setRegister of (mux (bit_and (eq v_10494 (eq (extract v_10474 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10494 (eq v_10481 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10476 57 65));
      setRegister af (bv_xor (extract (bv_xor v_10468 v_10474) 59 60) (extract v_10476 60 61));
      setRegister zf (zeroFlag v_10482);
      setRegister sf v_10481;
      setRegister cf (mux (notBool_ (eq (extract v_10476 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3193 : imm int) (v_3192 : Mem) => do
      v_13161 <- evaluateAddress v_3192;
      v_13162 <- eval (handleImmediateWithSignExtend v_3193 32 32);
      v_13164 <- eval (mi 64 (svalueMInt v_13162));
      v_13170 <- load v_13161 8;
      v_13172 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13164 (mi (bitwidthMInt v_13164) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_13170));
      v_13173 <- eval (extract v_13172 1 65);
      store v_13161 v_13173 8;
      v_13179 <- eval (extract v_13172 1 2);
      v_13188 <- eval (extract v_13164 0 1);
      v_13192 <- eval (eq (bv_xor v_13188 (mi (bitwidthMInt v_13188) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13192 (eq (extract v_13170 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13192 (eq v_13179 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13172 57 65));
      setRegister af (bv_xor (bv_xor (extract v_13162 27 28) (extract v_13170 59 60)) (extract v_13172 60 61));
      setRegister zf (zeroFlag v_13173);
      setRegister sf v_13179;
      setRegister cf (mux (notBool_ (eq (extract v_13172 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3197 : reg (bv 64)) (v_3196 : Mem) => do
      v_13207 <- evaluateAddress v_3196;
      v_13208 <- getRegister v_3197;
      v_13214 <- load v_13207 8;
      v_13216 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13208 (mi (bitwidthMInt v_13208) -1))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_13214));
      v_13217 <- eval (extract v_13216 1 65);
      store v_13207 v_13217 8;
      v_13223 <- eval (extract v_13216 1 2);
      v_13231 <- eval (extract v_13208 0 1);
      v_13235 <- eval (eq (bv_xor v_13231 (mi (bitwidthMInt v_13231) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13235 (eq (extract v_13214 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13235 (eq v_13223 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13216 57 65));
      setRegister af (bv_xor (extract (bv_xor v_13208 v_13214) 59 60) (extract v_13216 60 61));
      setRegister zf (zeroFlag v_13217);
      setRegister sf v_13223;
      setRegister cf (mux (notBool_ (eq (extract v_13216 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

def cmpb1 : instruction :=
  definst "cmpb" $ do
    pattern fun (v_3300 : imm int) al => do
      v_5198 <- eval (handleImmediateWithSignExtend v_3300 8 8);
      v_5204 <- getRegister rax;
      v_5207 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5198 (mi (bitwidthMInt v_5198) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) (extract v_5204 56 64)));
      v_5212 <- eval (extract v_5207 1 2);
      v_5213 <- eval (extract v_5207 1 9);
      v_5221 <- eval (extract v_5198 0 1);
      v_5225 <- eval (eq (bv_xor v_5221 (mi (bitwidthMInt v_5221) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5225 (eq (extract v_5204 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_5225 (eq v_5212 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_5213);
      setRegister af (bv_xor (bv_xor (extract v_5198 3 4) (extract v_5204 59 60)) (extract v_5207 4 5));
      setRegister zf (zeroFlag v_5213);
      setRegister sf v_5212;
      setRegister cf (mux (notBool_ (eq (extract v_5207 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3316 : imm int) (v_3318 : reg (bv 8)) => do
      v_5252 <- eval (handleImmediateWithSignExtend v_3316 8 8);
      v_5258 <- getRegister v_3318;
      v_5260 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5252 (mi (bitwidthMInt v_5252) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5258));
      v_5265 <- eval (extract v_5260 1 2);
      v_5266 <- eval (extract v_5260 1 9);
      v_5273 <- eval (extract v_5252 0 1);
      v_5277 <- eval (eq (bv_xor v_5273 (mi (bitwidthMInt v_5273) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5277 (eq (extract v_5258 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5277 (eq v_5265 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_5266);
      setRegister af (bv_xor (extract (bv_xor v_5252 v_5258) 3 4) (extract v_5260 4 5));
      setRegister zf (zeroFlag v_5266);
      setRegister sf v_5265;
      setRegister cf (mux (notBool_ (eq (extract v_5260 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3326 : reg (bv 8)) (v_3327 : reg (bv 8)) => do
      v_5296 <- getRegister v_3326;
      v_5302 <- getRegister v_3327;
      v_5304 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5296 (mi (bitwidthMInt v_5296) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5302));
      v_5309 <- eval (extract v_5304 1 2);
      v_5310 <- eval (extract v_5304 1 9);
      v_5317 <- eval (extract v_5296 0 1);
      v_5321 <- eval (eq (bv_xor v_5317 (mi (bitwidthMInt v_5317) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5321 (eq (extract v_5302 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5321 (eq v_5309 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_5310);
      setRegister af (bv_xor (extract (bv_xor v_5296 v_5302) 3 4) (extract v_5304 4 5));
      setRegister zf (zeroFlag v_5310);
      setRegister sf v_5309;
      setRegister cf (mux (notBool_ (eq (extract v_5304 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3304 : imm int) (v_3305 : Mem) => do
      v_8646 <- eval (handleImmediateWithSignExtend v_3304 8 8);
      v_8652 <- evaluateAddress v_3305;
      v_8653 <- load v_8652 1;
      v_8655 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8646 (mi (bitwidthMInt v_8646) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8653));
      v_8660 <- eval (extract v_8655 1 2);
      v_8661 <- eval (extract v_8655 1 9);
      v_8668 <- eval (extract v_8646 0 1);
      v_8672 <- eval (eq (bv_xor v_8668 (mi (bitwidthMInt v_8668) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8672 (eq (extract v_8653 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8672 (eq v_8660 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8661);
      setRegister af (bv_xor (extract (bv_xor v_8646 v_8653) 3 4) (extract v_8655 4 5));
      setRegister zf (zeroFlag v_8661);
      setRegister sf v_8660;
      setRegister cf (mux (notBool_ (eq (extract v_8655 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3309 : reg (bv 8)) (v_3308 : Mem) => do
      v_8687 <- getRegister v_3309;
      v_8693 <- evaluateAddress v_3308;
      v_8694 <- load v_8693 1;
      v_8696 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8687 (mi (bitwidthMInt v_8687) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8694));
      v_8701 <- eval (extract v_8696 1 2);
      v_8702 <- eval (extract v_8696 1 9);
      v_8709 <- eval (extract v_8687 0 1);
      v_8713 <- eval (eq (bv_xor v_8709 (mi (bitwidthMInt v_8709) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8713 (eq (extract v_8694 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8713 (eq v_8701 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8702);
      setRegister af (bv_xor (extract (bv_xor v_8687 v_8694) 3 4) (extract v_8696 4 5));
      setRegister zf (zeroFlag v_8702);
      setRegister sf v_8701;
      setRegister cf (mux (notBool_ (eq (extract v_8696 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3321 : Mem) (v_3322 : reg (bv 8)) => do
      v_8769 <- evaluateAddress v_3321;
      v_8770 <- load v_8769 1;
      v_8776 <- getRegister v_3322;
      v_8778 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8770 (mi (bitwidthMInt v_8770) -1))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8776));
      v_8783 <- eval (extract v_8778 1 2);
      v_8784 <- eval (extract v_8778 1 9);
      v_8791 <- eval (extract v_8770 0 1);
      v_8795 <- eval (eq (bv_xor v_8791 (mi (bitwidthMInt v_8791) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8795 (eq (extract v_8776 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8795 (eq v_8783 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8784);
      setRegister af (bv_xor (extract (bv_xor v_8770 v_8776) 3 4) (extract v_8778 4 5));
      setRegister zf (zeroFlag v_8784);
      setRegister sf v_8783;
      setRegister cf (mux (notBool_ (eq (extract v_8778 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

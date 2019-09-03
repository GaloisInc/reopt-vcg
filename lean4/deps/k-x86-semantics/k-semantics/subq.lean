def subq1 : instruction :=
  definst "subq" $ do
    pattern fun (v_3213 : imm int) (v_3214 : reg (bv 64)) => do
      v_7317 <- eval (handleImmediateWithSignExtend v_3213 32 32);
      v_7318 <- eval (leanSignExtend v_7317 64);
      v_7322 <- getRegister v_3214;
      v_7324 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7318 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7322));
      v_7329 <- eval (extract v_7324 1 2);
      v_7335 <- eval (extract v_7324 1 65);
      v_7341 <- eval (eq (bv_xor (extract v_7318 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3214) v_7335;
      setRegister of (mux (bit_and (eq v_7341 (eq (extract v_7322 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7341 (eq v_7329 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7324 57 65));
      setRegister zf (zeroFlag v_7335);
      setRegister af (bv_xor (bv_xor (extract v_7317 27 28) (extract v_7322 59 60)) (extract v_7324 60 61));
      setRegister sf v_7329;
      setRegister cf (mux (notBool_ (eq (extract v_7324 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3222 : reg (bv 64)) (v_3223 : reg (bv 64)) => do
      v_7361 <- getRegister v_3222;
      v_7365 <- getRegister v_3223;
      v_7367 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7361 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_7365));
      v_7372 <- eval (extract v_7367 1 2);
      v_7377 <- eval (extract v_7367 1 65);
      v_7383 <- eval (eq (bv_xor (extract v_7361 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3223) v_7377;
      setRegister of (mux (bit_and (eq v_7383 (eq (extract v_7365 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7383 (eq v_7372 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7367 57 65));
      setRegister zf (zeroFlag v_7377);
      setRegister af (bv_xor (extract (bv_xor v_7361 v_7365) 59 60) (extract v_7367 60 61));
      setRegister sf v_7372;
      setRegister cf (mux (notBool_ (eq (extract v_7367 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3218 : Mem) (v_3219 : reg (bv 64)) => do
      v_10549 <- evaluateAddress v_3218;
      v_10550 <- load v_10549 8;
      v_10554 <- getRegister v_3219;
      v_10556 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10550 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_10554));
      v_10561 <- eval (extract v_10556 1 2);
      v_10562 <- eval (extract v_10556 1 65);
      v_10572 <- eval (eq (bv_xor (extract v_10550 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3219) v_10562;
      setRegister of (mux (bit_and (eq v_10572 (eq (extract v_10554 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10572 (eq v_10561 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10556 57 65));
      setRegister af (bv_xor (extract (bv_xor v_10550 v_10554) 59 60) (extract v_10556 60 61));
      setRegister zf (zeroFlag v_10562);
      setRegister sf v_10561;
      setRegister cf (mux (notBool_ (eq (extract v_10556 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3205 : imm int) (v_3206 : Mem) => do
      v_13213 <- evaluateAddress v_3206;
      v_13214 <- eval (handleImmediateWithSignExtend v_3205 32 32);
      v_13215 <- eval (leanSignExtend v_13214 64);
      v_13219 <- load v_13213 8;
      v_13221 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13215 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_13219));
      v_13222 <- eval (extract v_13221 1 65);
      store v_13213 v_13222 8;
      v_13228 <- eval (extract v_13221 1 2);
      v_13239 <- eval (eq (bv_xor (extract v_13215 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13239 (eq (extract v_13219 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13239 (eq v_13228 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13221 57 65));
      setRegister af (bv_xor (bv_xor (extract v_13214 27 28) (extract v_13219 59 60)) (extract v_13221 60 61));
      setRegister zf (zeroFlag v_13222);
      setRegister sf v_13228;
      setRegister cf (mux (notBool_ (eq (extract v_13221 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3210 : reg (bv 64)) (v_3209 : Mem) => do
      v_13254 <- evaluateAddress v_3209;
      v_13255 <- getRegister v_3210;
      v_13259 <- load v_13254 8;
      v_13261 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13255 (expression.bv_nat 64 18446744073709551615))) (expression.bv_nat 65 1)) (concat (expression.bv_nat 1 0) v_13259));
      v_13262 <- eval (extract v_13261 1 65);
      store v_13254 v_13262 8;
      v_13268 <- eval (extract v_13261 1 2);
      v_13278 <- eval (eq (bv_xor (extract v_13255 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13278 (eq (extract v_13259 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13278 (eq v_13268 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13261 57 65));
      setRegister af (bv_xor (extract (bv_xor v_13255 v_13259) 59 60) (extract v_13261 60 61));
      setRegister zf (zeroFlag v_13262);
      setRegister sf v_13268;
      setRegister cf (mux (notBool_ (eq (extract v_13261 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

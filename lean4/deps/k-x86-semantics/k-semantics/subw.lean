def subw1 : instruction :=
  definst "subw" $ do
    pattern fun (v_3236 : imm int) ax => do
      v_7455 <- eval (handleImmediateWithSignExtend v_3236 16 16);
      v_7461 <- getRegister rax;
      v_7464 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7455 (mi (bitwidthMInt v_7455) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) (extract v_7461 48 64)));
      v_7469 <- eval (extract v_7464 1 2);
      v_7475 <- eval (extract v_7464 1 17);
      v_7479 <- eval (extract v_7455 0 1);
      v_7483 <- eval (eq (bv_xor v_7479 (mi (bitwidthMInt v_7479) -1)) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_7461 0 48) v_7475);
      setRegister of (mux (bit_and (eq v_7483 (eq (extract v_7461 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_7483 (eq v_7469 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7464 9 17));
      setRegister zf (zeroFlag v_7475);
      setRegister af (bv_xor (bv_xor (extract v_7455 11 12) (extract v_7461 59 60)) (extract v_7464 12 13));
      setRegister sf v_7469;
      setRegister cf (mux (notBool_ (eq (extract v_7464 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3248 : imm int) (v_3250 : reg (bv 16)) => do
      v_7509 <- eval (handleImmediateWithSignExtend v_3248 16 16);
      v_7515 <- getRegister v_3250;
      v_7517 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7509 (mi (bitwidthMInt v_7509) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7515));
      v_7522 <- eval (extract v_7517 1 2);
      v_7527 <- eval (extract v_7517 1 17);
      v_7531 <- eval (extract v_7509 0 1);
      v_7535 <- eval (eq (bv_xor v_7531 (mi (bitwidthMInt v_7531) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3250) v_7527;
      setRegister of (mux (bit_and (eq v_7535 (eq (extract v_7515 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7535 (eq v_7522 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7517 9 17));
      setRegister zf (zeroFlag v_7527);
      setRegister af (bv_xor (extract (bv_xor v_7509 v_7515) 11 12) (extract v_7517 12 13));
      setRegister sf v_7522;
      setRegister cf (mux (notBool_ (eq (extract v_7517 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3258 : reg (bv 16)) (v_3259 : reg (bv 16)) => do
      v_7555 <- getRegister v_3258;
      v_7561 <- getRegister v_3259;
      v_7563 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7555 (mi (bitwidthMInt v_7555) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7561));
      v_7568 <- eval (extract v_7563 1 2);
      v_7573 <- eval (extract v_7563 1 17);
      v_7577 <- eval (extract v_7555 0 1);
      v_7581 <- eval (eq (bv_xor v_7577 (mi (bitwidthMInt v_7577) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3259) v_7573;
      setRegister of (mux (bit_and (eq v_7581 (eq (extract v_7561 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7581 (eq v_7568 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7563 9 17));
      setRegister zf (zeroFlag v_7573);
      setRegister af (bv_xor (extract (bv_xor v_7555 v_7561) 11 12) (extract v_7563 12 13));
      setRegister sf v_7568;
      setRegister cf (mux (notBool_ (eq (extract v_7563 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3253 : Mem) (v_3254 : reg (bv 16)) => do
      v_10534 <- evaluateAddress v_3253;
      v_10535 <- load v_10534 2;
      v_10541 <- getRegister v_3254;
      v_10543 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10535 (mi (bitwidthMInt v_10535) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_10541));
      v_10548 <- eval (extract v_10543 1 2);
      v_10553 <- eval (extract v_10543 1 17);
      v_10557 <- eval (extract v_10535 0 1);
      v_10561 <- eval (eq (bv_xor v_10557 (mi (bitwidthMInt v_10557) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3254) v_10553;
      setRegister of (mux (bit_and (eq v_10561 (eq (extract v_10541 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10561 (eq v_10548 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10543 9 17));
      setRegister zf (zeroFlag v_10553);
      setRegister af (bv_xor (extract (bv_xor v_10535 v_10541) 11 12) (extract v_10543 12 13));
      setRegister sf v_10548;
      setRegister cf (mux (notBool_ (eq (extract v_10543 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3241 : imm int) (v_3240 : Mem) => do
      v_13250 <- evaluateAddress v_3240;
      v_13251 <- eval (handleImmediateWithSignExtend v_3241 16 16);
      v_13257 <- load v_13250 2;
      v_13259 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13251 (mi (bitwidthMInt v_13251) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_13257));
      v_13260 <- eval (extract v_13259 1 17);
      store v_13250 v_13260 2;
      v_13266 <- eval (extract v_13259 1 2);
      v_13274 <- eval (extract v_13251 0 1);
      v_13278 <- eval (eq (bv_xor v_13274 (mi (bitwidthMInt v_13274) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13278 (eq (extract v_13257 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13278 (eq v_13266 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13259 9 17));
      setRegister af (bv_xor (extract (bv_xor v_13251 v_13257) 11 12) (extract v_13259 12 13));
      setRegister zf (zeroFlag v_13260);
      setRegister sf v_13266;
      setRegister cf (mux (notBool_ (eq (extract v_13259 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3245 : reg (bv 16)) (v_3244 : Mem) => do
      v_13293 <- evaluateAddress v_3244;
      v_13294 <- getRegister v_3245;
      v_13300 <- load v_13293 2;
      v_13302 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13294 (mi (bitwidthMInt v_13294) -1))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_13300));
      v_13303 <- eval (extract v_13302 1 17);
      store v_13293 v_13303 2;
      v_13309 <- eval (extract v_13302 1 2);
      v_13317 <- eval (extract v_13294 0 1);
      v_13321 <- eval (eq (bv_xor v_13317 (mi (bitwidthMInt v_13317) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13321 (eq (extract v_13300 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13321 (eq v_13309 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13302 9 17));
      setRegister af (bv_xor (extract (bv_xor v_13294 v_13300) 11 12) (extract v_13302 12 13));
      setRegister zf (zeroFlag v_13303);
      setRegister sf v_13309;
      setRegister cf (mux (notBool_ (eq (extract v_13302 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

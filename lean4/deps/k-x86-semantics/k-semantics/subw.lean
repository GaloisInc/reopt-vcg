def subw1 : instruction :=
  definst "subw" $ do
    pattern fun (v_3249 : imm int) ax => do
      v_7493 <- eval (handleImmediateWithSignExtend v_3249 16 16);
      v_7497 <- getRegister rax;
      v_7500 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7493 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) (extract v_7497 48 64)));
      v_7505 <- eval (extract v_7500 1 2);
      v_7511 <- eval (extract v_7500 1 17);
      v_7517 <- eval (eq (bv_xor (extract v_7493 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_7497 0 48) v_7511);
      setRegister of (mux (bit_and (eq v_7517 (eq (extract v_7497 48 49) (expression.bv_nat 1 1))) (notBool_ (eq v_7517 (eq v_7505 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7500 9 17));
      setRegister zf (zeroFlag v_7511);
      setRegister af (bv_xor (bv_xor (extract v_7493 11 12) (extract v_7497 59 60)) (extract v_7500 12 13));
      setRegister sf v_7505;
      setRegister cf (mux (notBool_ (eq (extract v_7500 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3261 : imm int) (v_3263 : reg (bv 16)) => do
      v_7543 <- eval (handleImmediateWithSignExtend v_3261 16 16);
      v_7547 <- getRegister v_3263;
      v_7549 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7543 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7547));
      v_7554 <- eval (extract v_7549 1 2);
      v_7559 <- eval (extract v_7549 1 17);
      v_7565 <- eval (eq (bv_xor (extract v_7543 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3263) v_7559;
      setRegister of (mux (bit_and (eq v_7565 (eq (extract v_7547 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7565 (eq v_7554 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7549 9 17));
      setRegister zf (zeroFlag v_7559);
      setRegister af (bv_xor (extract (bv_xor v_7543 v_7547) 11 12) (extract v_7549 12 13));
      setRegister sf v_7554;
      setRegister cf (mux (notBool_ (eq (extract v_7549 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3271 : reg (bv 16)) (v_3272 : reg (bv 16)) => do
      v_7585 <- getRegister v_3271;
      v_7589 <- getRegister v_3272;
      v_7591 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_7585 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_7589));
      v_7596 <- eval (extract v_7591 1 2);
      v_7601 <- eval (extract v_7591 1 17);
      v_7607 <- eval (eq (bv_xor (extract v_7585 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3272) v_7601;
      setRegister of (mux (bit_and (eq v_7607 (eq (extract v_7589 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7607 (eq v_7596 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_7591 9 17));
      setRegister zf (zeroFlag v_7601);
      setRegister af (bv_xor (extract (bv_xor v_7585 v_7589) 11 12) (extract v_7591 12 13));
      setRegister sf v_7596;
      setRegister cf (mux (notBool_ (eq (extract v_7591 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3266 : Mem) (v_3267 : reg (bv 16)) => do
      v_10636 <- evaluateAddress v_3266;
      v_10637 <- load v_10636 2;
      v_10641 <- getRegister v_3267;
      v_10643 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_10637 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_10641));
      v_10648 <- eval (extract v_10643 1 2);
      v_10649 <- eval (extract v_10643 1 17);
      v_10659 <- eval (eq (bv_xor (extract v_10637 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3267) v_10649;
      setRegister of (mux (bit_and (eq v_10659 (eq (extract v_10641 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_10659 (eq v_10648 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_10643 9 17));
      setRegister af (bv_xor (extract (bv_xor v_10637 v_10641) 11 12) (extract v_10643 12 13));
      setRegister zf (zeroFlag v_10649);
      setRegister sf v_10648;
      setRegister cf (mux (notBool_ (eq (extract v_10643 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3253 : imm int) (v_3254 : Mem) => do
      v_13293 <- evaluateAddress v_3254;
      v_13294 <- eval (handleImmediateWithSignExtend v_3253 16 16);
      v_13298 <- load v_13293 2;
      v_13300 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13294 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_13298));
      v_13301 <- eval (extract v_13300 1 17);
      store v_13293 v_13301 2;
      v_13307 <- eval (extract v_13300 1 2);
      v_13317 <- eval (eq (bv_xor (extract v_13294 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13317 (eq (extract v_13298 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13317 (eq v_13307 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13300 9 17));
      setRegister af (bv_xor (extract (bv_xor v_13294 v_13298) 11 12) (extract v_13300 12 13));
      setRegister zf (zeroFlag v_13301);
      setRegister sf v_13307;
      setRegister cf (mux (notBool_ (eq (extract v_13300 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3258 : reg (bv 16)) (v_3257 : Mem) => do
      v_13332 <- evaluateAddress v_3257;
      v_13333 <- getRegister v_3258;
      v_13337 <- load v_13332 2;
      v_13339 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_13333 (expression.bv_nat 16 65535))) (expression.bv_nat 17 1)) (concat (expression.bv_nat 1 0) v_13337));
      v_13340 <- eval (extract v_13339 1 17);
      store v_13332 v_13340 2;
      v_13346 <- eval (extract v_13339 1 2);
      v_13356 <- eval (eq (bv_xor (extract v_13333 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_13356 (eq (extract v_13337 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13356 (eq v_13346 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag (extract v_13339 9 17));
      setRegister af (bv_xor (extract (bv_xor v_13333 v_13337) 11 12) (extract v_13339 12 13));
      setRegister zf (zeroFlag v_13340);
      setRegister sf v_13346;
      setRegister cf (mux (notBool_ (eq (extract v_13339 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

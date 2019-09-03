def cmpb1 : instruction :=
  definst "cmpb" $ do
    pattern fun (v_3312 : imm int) al => do
      v_5211 <- eval (handleImmediateWithSignExtend v_3312 8 8);
      v_5215 <- getRegister rax;
      v_5218 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5211 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) (extract v_5215 56 64)));
      v_5223 <- eval (extract v_5218 1 2);
      v_5224 <- eval (extract v_5218 1 9);
      v_5234 <- eval (eq (bv_xor (extract v_5211 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5234 (eq (extract v_5215 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_5234 (eq v_5223 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_5224);
      setRegister af (bv_xor (bv_xor (extract v_5211 3 4) (extract v_5215 59 60)) (extract v_5218 4 5));
      setRegister zf (zeroFlag v_5224);
      setRegister sf v_5223;
      setRegister cf (mux (notBool_ (eq (extract v_5218 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3328 : imm int) (v_3330 : reg (bv 8)) => do
      v_5261 <- eval (handleImmediateWithSignExtend v_3328 8 8);
      v_5265 <- getRegister v_3330;
      v_5267 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5261 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5265));
      v_5272 <- eval (extract v_5267 1 2);
      v_5273 <- eval (extract v_5267 1 9);
      v_5282 <- eval (eq (bv_xor (extract v_5261 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5282 (eq (extract v_5265 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5282 (eq v_5272 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_5273);
      setRegister af (bv_xor (extract (bv_xor v_5261 v_5265) 3 4) (extract v_5267 4 5));
      setRegister zf (zeroFlag v_5273);
      setRegister sf v_5272;
      setRegister cf (mux (notBool_ (eq (extract v_5267 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3338 : reg (bv 8)) (v_3339 : reg (bv 8)) => do
      v_5301 <- getRegister v_3338;
      v_5305 <- getRegister v_3339;
      v_5307 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_5301 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_5305));
      v_5312 <- eval (extract v_5307 1 2);
      v_5313 <- eval (extract v_5307 1 9);
      v_5322 <- eval (eq (bv_xor (extract v_5301 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_5322 (eq (extract v_5305 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_5322 (eq v_5312 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_5313);
      setRegister af (bv_xor (extract (bv_xor v_5301 v_5305) 3 4) (extract v_5307 4 5));
      setRegister zf (zeroFlag v_5313);
      setRegister sf v_5312;
      setRegister cf (mux (notBool_ (eq (extract v_5307 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3317 : imm int) (v_3316 : Mem) => do
      v_8619 <- eval (handleImmediateWithSignExtend v_3317 8 8);
      v_8623 <- evaluateAddress v_3316;
      v_8624 <- load v_8623 1;
      v_8626 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8619 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8624));
      v_8631 <- eval (extract v_8626 1 2);
      v_8632 <- eval (extract v_8626 1 9);
      v_8641 <- eval (eq (bv_xor (extract v_8619 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8641 (eq (extract v_8624 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8641 (eq v_8631 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8632);
      setRegister af (bv_xor (extract (bv_xor v_8619 v_8624) 3 4) (extract v_8626 4 5));
      setRegister zf (zeroFlag v_8632);
      setRegister sf v_8631;
      setRegister cf (mux (notBool_ (eq (extract v_8626 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3321 : reg (bv 8)) (v_3320 : Mem) => do
      v_8656 <- getRegister v_3321;
      v_8660 <- evaluateAddress v_3320;
      v_8661 <- load v_8660 1;
      v_8663 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8656 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8661));
      v_8668 <- eval (extract v_8663 1 2);
      v_8669 <- eval (extract v_8663 1 9);
      v_8678 <- eval (eq (bv_xor (extract v_8656 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8678 (eq (extract v_8661 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8678 (eq v_8668 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8669);
      setRegister af (bv_xor (extract (bv_xor v_8656 v_8661) 3 4) (extract v_8663 4 5));
      setRegister zf (zeroFlag v_8669);
      setRegister sf v_8668;
      setRegister cf (mux (notBool_ (eq (extract v_8663 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3333 : Mem) (v_3334 : reg (bv 8)) => do
      v_8730 <- evaluateAddress v_3333;
      v_8731 <- load v_8730 1;
      v_8735 <- getRegister v_3334;
      v_8737 <- eval (add (add (concat (expression.bv_nat 1 0) (bv_xor v_8731 (expression.bv_nat 8 255))) (expression.bv_nat 9 1)) (concat (expression.bv_nat 1 0) v_8735));
      v_8742 <- eval (extract v_8737 1 2);
      v_8743 <- eval (extract v_8737 1 9);
      v_8752 <- eval (eq (bv_xor (extract v_8731 0 1) (expression.bv_nat 1 1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_8752 (eq (extract v_8735 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8752 (eq v_8742 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8743);
      setRegister af (bv_xor (extract (bv_xor v_8731 v_8735) 3 4) (extract v_8737 4 5));
      setRegister zf (zeroFlag v_8743);
      setRegister sf v_8742;
      setRegister cf (mux (notBool_ (eq (extract v_8737 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

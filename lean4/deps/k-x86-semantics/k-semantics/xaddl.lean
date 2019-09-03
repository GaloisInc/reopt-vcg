def xaddl1 : instruction :=
  definst "xaddl" $ do
    pattern fun (v_2619 : reg (bv 32)) (v_2620 : reg (bv 32)) => do
      v_3929 <- eval (eq (eq (convToRegKeysHelper (convSubRegsToRegs v_2619)) (convToRegKeysHelper (convSubRegsToRegs v_2620))) bit_zero);
      v_3930 <- getRegister v_2619;
      v_3932 <- getRegister v_2620;
      v_3934 <- eval (add (concat (expression.bv_nat 1 0) v_3930) (concat (expression.bv_nat 1 0) v_3932));
      v_3936 <- eval (extract v_3934 1 2);
      v_3937 <- eval (extract v_3934 1 33);
      v_3943 <- eval (extract v_3934 28 29);
      v_3977 <- eval (eq (extract v_3930 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2620) v_3937;
      setRegister (lhs.of_reg v_2619) v_3932;
      setRegister of (mux (bit_and (eq v_3977 (eq (extract v_3932 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_3977 (eq v_3936 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_3934 32 33) (expression.bv_nat 1 1)) (eq (extract v_3934 31 32) (expression.bv_nat 1 1)))) (eq (extract v_3934 30 31) (expression.bv_nat 1 1)))) (eq (extract v_3934 29 30) (expression.bv_nat 1 1)))) (eq v_3943 (expression.bv_nat 1 1)))) (eq (extract v_3934 27 28) (expression.bv_nat 1 1)))) (eq (extract v_3934 26 27) (expression.bv_nat 1 1)))) (eq (extract v_3934 25 26) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (bv_xor (bv_xor (extract v_3930 27 28) (extract v_3932 27 28)) v_3943);
      setRegister zf (mux (eq v_3937 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_3936;
      setRegister cf (extract v_3934 0 1);
      pure ()
    pat_end;
    pattern fun (v_2624 : reg (bv 32)) (v_2625 : reg (bv 32)) => do
      v_3998 <- eval (eq (convToRegKeysHelper (convSubRegsToRegs v_2624)) (convToRegKeysHelper (convSubRegsToRegs v_2625)));
      v_3999 <- getRegister v_2625;
      v_4001 <- eval (add (concat (expression.bv_nat 1 0) v_3999) (concat (expression.bv_nat 1 0) v_3999));
      v_4003 <- eval (extract v_4001 1 2);
      v_4004 <- eval (extract v_4001 1 33);
      v_4007 <- eval (extract v_4001 28 29);
      setRegister (lhs.of_reg v_2625) v_4004;
      setRegister of (mux (notBool_ (eq (eq (extract v_3999 0 1) (expression.bv_nat 1 1)) (eq v_4003 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4001 32 33) (expression.bv_nat 1 1)) (eq (extract v_4001 31 32) (expression.bv_nat 1 1)))) (eq (extract v_4001 30 31) (expression.bv_nat 1 1)))) (eq (extract v_4001 29 30) (expression.bv_nat 1 1)))) (eq v_4007 (expression.bv_nat 1 1)))) (eq (extract v_4001 27 28) (expression.bv_nat 1 1)))) (eq (extract v_4001 26 27) (expression.bv_nat 1 1)))) (eq (extract v_4001 25 26) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af v_4007;
      setRegister zf (mux (eq v_4004 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister sf v_4003;
      setRegister cf (extract v_4001 0 1);
      pure ()
    pat_end;
    pattern fun (v_2615 : reg (bv 32)) (v_2614 : Mem) => do
      v_7388 <- evaluateAddress v_2614;
      v_7389 <- getRegister v_2615;
      v_7391 <- load v_7388 4;
      v_7393 <- eval (add (concat (expression.bv_nat 1 0) v_7389) (concat (expression.bv_nat 1 0) v_7391));
      v_7394 <- eval (extract v_7393 1 33);
      store v_7388 v_7394 4;
      v_7397 <- eval (extract v_7393 1 2);
      v_7401 <- eval (extract v_7393 28 29);
      v_7437 <- eval (eq (extract v_7389 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2615) v_7391;
      setRegister of (mux (bit_and (eq v_7437 (eq (extract v_7391 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7437 (eq v_7397 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7393 32 33) (expression.bv_nat 1 1)) (eq (extract v_7393 31 32) (expression.bv_nat 1 1)))) (eq (extract v_7393 30 31) (expression.bv_nat 1 1)))) (eq (extract v_7393 29 30) (expression.bv_nat 1 1)))) (eq v_7401 (expression.bv_nat 1 1)))) (eq (extract v_7393 27 28) (expression.bv_nat 1 1)))) (eq (extract v_7393 26 27) (expression.bv_nat 1 1)))) (eq (extract v_7393 25 26) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_7394 (expression.bv_nat 32 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (bv_xor (bv_xor (extract v_7389 27 28) (extract v_7391 27 28)) v_7401);
      setRegister sf v_7397;
      setRegister cf (extract v_7393 0 1);
      pure ()
    pat_end

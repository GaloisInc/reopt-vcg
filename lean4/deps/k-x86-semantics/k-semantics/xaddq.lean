def xaddq1 : instruction :=
  definst "xaddq" $ do
    pattern fun (v_2632 : reg (bv 64)) (v_2633 : reg (bv 64)) => do
      v_4061 <- eval (eq (eq (convToRegKeysHelper (convSubRegsToRegs v_2632)) (convToRegKeysHelper (convSubRegsToRegs v_2633))) bit_zero);
      v_4062 <- getRegister v_2632;
      v_4064 <- getRegister v_2633;
      v_4066 <- eval (add (concat (expression.bv_nat 1 0) v_4062) (concat (expression.bv_nat 1 0) v_4064));
      v_4068 <- eval (extract v_4066 1 2);
      v_4072 <- eval (extract v_4066 60 61);
      v_4105 <- eval (extract v_4066 1 65);
      v_4109 <- eval (eq (extract v_4062 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2633) v_4105;
      setRegister (lhs.of_reg v_2632) v_4064;
      setRegister of (mux (bit_and (eq v_4109 (eq (extract v_4064 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_4109 (eq v_4068 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_4105 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4066 64 65) (expression.bv_nat 1 1)) (eq (extract v_4066 63 64) (expression.bv_nat 1 1)))) (eq (extract v_4066 62 63) (expression.bv_nat 1 1)))) (eq (extract v_4066 61 62) (expression.bv_nat 1 1)))) (eq v_4072 (expression.bv_nat 1 1)))) (eq (extract v_4066 59 60) (expression.bv_nat 1 1)))) (eq (extract v_4066 58 59) (expression.bv_nat 1 1)))) (eq (extract v_4066 57 58) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (bv_xor (bv_xor (extract v_4062 59 60) (extract v_4064 59 60)) v_4072);
      setRegister sf v_4068;
      setRegister cf (extract v_4066 0 1);
      pure ()
    pat_end;
    pattern fun (v_2637 : reg (bv 64)) (v_2638 : reg (bv 64)) => do
      v_4130 <- eval (eq (convToRegKeysHelper (convSubRegsToRegs v_2637)) (convToRegKeysHelper (convSubRegsToRegs v_2638)));
      v_4131 <- getRegister v_2638;
      v_4133 <- eval (add (concat (expression.bv_nat 1 0) v_4131) (concat (expression.bv_nat 1 0) v_4131));
      v_4135 <- eval (extract v_4133 1 2);
      v_4136 <- eval (extract v_4133 60 61);
      v_4137 <- eval (extract v_4133 1 65);
      setRegister (lhs.of_reg v_2638) v_4137;
      setRegister of (mux (notBool_ (eq (eq (extract v_4131 0 1) (expression.bv_nat 1 1)) (eq v_4135 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_4133 64 65) (expression.bv_nat 1 1)) (eq (extract v_4133 63 64) (expression.bv_nat 1 1)))) (eq (extract v_4133 62 63) (expression.bv_nat 1 1)))) (eq (extract v_4133 61 62) (expression.bv_nat 1 1)))) (eq v_4136 (expression.bv_nat 1 1)))) (eq (extract v_4133 59 60) (expression.bv_nat 1 1)))) (eq (extract v_4133 58 59) (expression.bv_nat 1 1)))) (eq (extract v_4133 57 58) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_4137 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af v_4136;
      setRegister sf v_4135;
      setRegister cf (extract v_4133 0 1);
      pure ()
    pat_end;
    pattern fun (v_2628 : reg (bv 64)) (v_2629 : Mem) => do
      v_7453 <- evaluateAddress v_2629;
      v_7454 <- getRegister v_2628;
      v_7456 <- load v_7453 8;
      v_7458 <- eval (add (concat (expression.bv_nat 1 0) v_7454) (concat (expression.bv_nat 1 0) v_7456));
      v_7459 <- eval (extract v_7458 1 65);
      store v_7453 v_7459 8;
      v_7462 <- eval (extract v_7458 1 2);
      v_7466 <- eval (extract v_7458 60 61);
      v_7502 <- eval (eq (extract v_7454 0 1) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_2628) v_7456;
      setRegister of (mux (bit_and (eq v_7502 (eq (extract v_7456 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_7502 (eq v_7462 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (mux (notBool_ (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (notBool_ (eq (eq (extract v_7458 64 65) (expression.bv_nat 1 1)) (eq (extract v_7458 63 64) (expression.bv_nat 1 1)))) (eq (extract v_7458 62 63) (expression.bv_nat 1 1)))) (eq (extract v_7458 61 62) (expression.bv_nat 1 1)))) (eq v_7466 (expression.bv_nat 1 1)))) (eq (extract v_7458 59 60) (expression.bv_nat 1 1)))) (eq (extract v_7458 58 59) (expression.bv_nat 1 1)))) (eq (extract v_7458 57 58) (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister zf (mux (eq v_7459 (expression.bv_nat 64 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister af (bv_xor (bv_xor (extract v_7454 59 60) (extract v_7456 59 60)) v_7466);
      setRegister sf v_7462;
      setRegister cf (extract v_7458 0 1);
      pure ()
    pat_end

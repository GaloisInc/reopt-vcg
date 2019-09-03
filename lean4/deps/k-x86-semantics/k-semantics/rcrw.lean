def rcrw1 : instruction :=
  definst "rcrw" $ do
    pattern fun cl (v_2537 : reg (bv 16)) => do
      v_4652 <- getRegister cf;
      v_4655 <- getRegister v_2537;
      v_4657 <- getRegister rcx;
      v_4661 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4657 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4663 <- eval (rorHelper (concat (mux (eq v_4652 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4655) (uvalueMInt v_4661) 0);
      v_4665 <- eval (extract v_4661 9 17);
      v_4666 <- eval (eq v_4665 (expression.bv_nat 8 1));
      v_4675 <- eval (eq v_4665 (expression.bv_nat 8 0));
      v_4678 <- getRegister of;
      setRegister (lhs.of_reg v_2537) (extract v_4663 1 17);
      setRegister of (mux (bit_or (bit_and v_4666 (notBool_ (eq (eq (extract v_4663 1 2) (expression.bv_nat 1 1)) (eq (extract v_4663 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4666) (bit_or (bit_and (notBool_ v_4675) undef) (bit_and v_4675 (eq v_4678 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4663 0 1);
      pure ()
    pat_end;
    pattern fun (v_2538 : imm int) (v_2542 : reg (bv 16)) => do
      v_4689 <- getRegister cf;
      v_4692 <- getRegister v_2542;
      v_4697 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2538 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4699 <- eval (rorHelper (concat (mux (eq v_4689 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4692) (uvalueMInt v_4697) 0);
      v_4701 <- eval (extract v_4697 9 17);
      v_4702 <- eval (eq v_4701 (expression.bv_nat 8 1));
      v_4711 <- eval (eq v_4701 (expression.bv_nat 8 0));
      v_4714 <- getRegister of;
      setRegister (lhs.of_reg v_2542) (extract v_4699 1 17);
      setRegister of (mux (bit_or (bit_and v_4702 (notBool_ (eq (eq (extract v_4699 1 2) (expression.bv_nat 1 1)) (eq (extract v_4699 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4702) (bit_or (bit_and (notBool_ v_4711) undef) (bit_and v_4711 (eq v_4714 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4699 0 1);
      pure ()
    pat_end;
    pattern fun $0x1 (v_2546 : reg (bv 16)) => do
      v_4725 <- getRegister cf;
      v_4728 <- getRegister v_2546;
      v_4729 <- eval (concat (mux (eq v_4725 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4728);
      v_4731 <- eval (bitwidthMInt v_4729);
      v_4732 <- eval (sub v_4731 1);
      v_4736 <- eval (add (lshr v_4729 1) (concat (extract v_4729 v_4732 v_4731) (mi v_4732 0)));
      setRegister (lhs.of_reg v_2546) (extract v_4736 1 17);
      setRegister of (mux (notBool_ (eq (eq (extract v_4736 1 2) (expression.bv_nat 1 1)) (eq (extract v_4736 2 3) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4736 0 1);
      pure ()
    pat_end;
    pattern fun cl (v_2524 : Mem) => do
      v_14052 <- evaluateAddress v_2524;
      v_14053 <- getRegister cf;
      v_14056 <- load v_14052 2;
      v_14058 <- getRegister rcx;
      v_14062 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_14058 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_14064 <- eval (rorHelper (concat (mux (eq v_14053 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_14056) (uvalueMInt v_14062) 0);
      store v_14052 (extract v_14064 1 17) 2;
      v_14068 <- eval (extract v_14062 9 17);
      v_14069 <- eval (eq v_14068 (expression.bv_nat 8 1));
      v_14078 <- eval (eq v_14068 (expression.bv_nat 8 0));
      v_14081 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14069 (notBool_ (eq (eq (extract v_14064 1 2) (expression.bv_nat 1 1)) (eq (extract v_14064 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14069) (bit_or (bit_and (notBool_ v_14078) undef) (bit_and v_14078 (eq v_14081 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_14064 0 1);
      pure ()
    pat_end;
    pattern fun (v_2527 : imm int) (v_2528 : Mem) => do
      v_14090 <- evaluateAddress v_2528;
      v_14091 <- getRegister cf;
      v_14094 <- load v_14090 2;
      v_14099 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2527 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_14101 <- eval (rorHelper (concat (mux (eq v_14091 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_14094) (uvalueMInt v_14099) 0);
      store v_14090 (extract v_14101 1 17) 2;
      v_14105 <- eval (extract v_14099 9 17);
      v_14106 <- eval (eq v_14105 (expression.bv_nat 8 1));
      v_14115 <- eval (eq v_14105 (expression.bv_nat 8 0));
      v_14118 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14106 (notBool_ (eq (eq (extract v_14101 1 2) (expression.bv_nat 1 1)) (eq (extract v_14101 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14106) (bit_or (bit_and (notBool_ v_14115) undef) (bit_and v_14115 (eq v_14118 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_14101 0 1);
      pure ()
    pat_end

def rorb1 : instruction :=
  definst "rorb" $ do
    pattern fun cl (v_2679 : reg (bv 8)) => do
      v_5278 <- getRegister rcx;
      v_5280 <- eval (bv_and (extract v_5278 56 64) (expression.bv_nat 8 31));
      v_5281 <- eval (eq v_5280 (expression.bv_nat 8 0));
      v_5282 <- eval (notBool_ v_5281);
      v_5283 <- getRegister v_2679;
      v_5285 <- eval (rorHelper v_5283 (uvalueMInt v_5280) 0);
      v_5287 <- eval (eq (extract v_5285 0 1) (expression.bv_nat 1 1));
      v_5289 <- getRegister cf;
      v_5294 <- eval (eq v_5280 (expression.bv_nat 8 1));
      v_5302 <- getRegister of;
      setRegister (lhs.of_reg v_2679) v_5285;
      setRegister of (mux (bit_or (bit_and v_5294 (notBool_ (eq v_5287 (eq (extract v_5285 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5294) (bit_or (bit_and v_5282 undef) (bit_and v_5281 (eq v_5302 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5282 v_5287) (bit_and v_5281 (eq v_5289 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2682 : imm int) (v_2684 : reg (bv 8)) => do
      v_5313 <- eval (bv_and (handleImmediateWithSignExtend v_2682 8 8) (expression.bv_nat 8 31));
      v_5314 <- eval (eq v_5313 (expression.bv_nat 8 0));
      v_5315 <- eval (notBool_ v_5314);
      v_5316 <- getRegister v_2684;
      v_5318 <- eval (rorHelper v_5316 (uvalueMInt v_5313) 0);
      v_5320 <- eval (eq (extract v_5318 0 1) (expression.bv_nat 1 1));
      v_5322 <- getRegister cf;
      v_5327 <- eval (eq v_5313 (expression.bv_nat 8 1));
      v_5335 <- getRegister of;
      setRegister (lhs.of_reg v_2684) v_5318;
      setRegister of (mux (bit_or (bit_and v_5327 (notBool_ (eq v_5320 (eq (extract v_5318 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5327) (bit_or (bit_and v_5315 undef) (bit_and v_5314 (eq v_5335 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5315 v_5320) (bit_and v_5314 (eq v_5322 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2688 : reg (bv 8)) => do
      v_5345 <- getRegister v_2688;
      v_5349 <- eval (add (lshr v_5345 1) (concat (extract v_5345 7 8) (expression.bv_nat 7 0)));
      v_5350 <- eval (extract v_5349 0 1);
      setRegister (lhs.of_reg v_2688) v_5349;
      setRegister of (mux (notBool_ (eq (eq v_5350 (expression.bv_nat 1 1)) (eq (extract v_5349 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5350;
      pure ()
    pat_end;
    pattern fun cl (v_2668 : Mem) => do
      v_14655 <- evaluateAddress v_2668;
      v_14656 <- load v_14655 1;
      v_14657 <- getRegister rcx;
      v_14659 <- eval (bv_and (extract v_14657 56 64) (expression.bv_nat 8 31));
      v_14661 <- eval (rorHelper v_14656 (uvalueMInt v_14659) 0);
      store v_14655 v_14661 1;
      v_14663 <- eval (eq v_14659 (expression.bv_nat 8 0));
      v_14664 <- eval (notBool_ v_14663);
      v_14666 <- eval (eq (extract v_14661 0 1) (expression.bv_nat 1 1));
      v_14668 <- getRegister cf;
      v_14673 <- eval (eq v_14659 (expression.bv_nat 8 1));
      v_14681 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14673 (notBool_ (eq v_14666 (eq (extract v_14661 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14673) (bit_or (bit_and v_14664 undef) (bit_and v_14663 (eq v_14681 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14664 v_14666) (bit_and v_14663 (eq v_14668 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2672 : imm int) (v_2671 : Mem) => do
      v_14690 <- evaluateAddress v_2671;
      v_14691 <- load v_14690 1;
      v_14693 <- eval (bv_and (handleImmediateWithSignExtend v_2672 8 8) (expression.bv_nat 8 31));
      v_14695 <- eval (rorHelper v_14691 (uvalueMInt v_14693) 0);
      store v_14690 v_14695 1;
      v_14697 <- eval (eq v_14693 (expression.bv_nat 8 0));
      v_14698 <- eval (notBool_ v_14697);
      v_14700 <- eval (eq (extract v_14695 0 1) (expression.bv_nat 1 1));
      v_14702 <- getRegister cf;
      v_14707 <- eval (eq v_14693 (expression.bv_nat 8 1));
      v_14715 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14707 (notBool_ (eq v_14700 (eq (extract v_14695 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14707) (bit_or (bit_and v_14698 undef) (bit_and v_14697 (eq v_14715 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14698 v_14700) (bit_and v_14697 (eq v_14702 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

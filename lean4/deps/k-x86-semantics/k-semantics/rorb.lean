def rorb1 : instruction :=
  definst "rorb" $ do
    pattern fun cl (v_2668 : reg (bv 8)) => do
      v_5243 <- getRegister rcx;
      v_5245 <- eval (bv_and (extract v_5243 56 64) (expression.bv_nat 8 31));
      v_5246 <- eval (eq v_5245 (expression.bv_nat 8 0));
      v_5247 <- eval (notBool_ v_5246);
      v_5248 <- getRegister v_2668;
      v_5250 <- eval (rorHelper v_5248 (uvalueMInt v_5245) 0);
      v_5252 <- eval (eq (extract v_5250 0 1) (expression.bv_nat 1 1));
      v_5254 <- getRegister cf;
      v_5259 <- eval (eq v_5245 (expression.bv_nat 8 1));
      v_5267 <- getRegister of;
      setRegister (lhs.of_reg v_2668) v_5250;
      setRegister of (mux (bit_or (bit_and v_5259 (notBool_ (eq v_5252 (eq (extract v_5250 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5259) (bit_or (bit_and v_5247 undef) (bit_and v_5246 (eq v_5267 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5247 v_5252) (bit_and v_5246 (eq v_5254 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2669 : imm int) (v_2673 : reg (bv 8)) => do
      v_5278 <- eval (bv_and (handleImmediateWithSignExtend v_2669 8 8) (expression.bv_nat 8 31));
      v_5279 <- eval (eq v_5278 (expression.bv_nat 8 0));
      v_5280 <- eval (notBool_ v_5279);
      v_5281 <- getRegister v_2673;
      v_5283 <- eval (rorHelper v_5281 (uvalueMInt v_5278) 0);
      v_5285 <- eval (eq (extract v_5283 0 1) (expression.bv_nat 1 1));
      v_5287 <- getRegister cf;
      v_5292 <- eval (eq v_5278 (expression.bv_nat 8 1));
      v_5300 <- getRegister of;
      setRegister (lhs.of_reg v_2673) v_5283;
      setRegister of (mux (bit_or (bit_and v_5292 (notBool_ (eq v_5285 (eq (extract v_5283 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_5292) (bit_or (bit_and v_5280 undef) (bit_and v_5279 (eq v_5300 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_5280 v_5285) (bit_and v_5279 (eq v_5287 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2677 : reg (bv 8)) => do
      v_5310 <- getRegister v_2677;
      v_5312 <- eval (bitwidthMInt v_5310);
      v_5313 <- eval (sub v_5312 1);
      v_5317 <- eval (add (lshr v_5310 1) (concat (extract v_5310 v_5313 v_5312) (mi v_5313 0)));
      v_5318 <- eval (extract v_5317 0 1);
      setRegister (lhs.of_reg v_2677) v_5317;
      setRegister of (mux (notBool_ (eq (eq v_5318 (expression.bv_nat 1 1)) (eq (extract v_5317 1 2) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_5318;
      pure ()
    pat_end;
    pattern fun cl (v_2655 : Mem) => do
      v_14789 <- evaluateAddress v_2655;
      v_14790 <- load v_14789 1;
      v_14791 <- getRegister rcx;
      v_14793 <- eval (bv_and (extract v_14791 56 64) (expression.bv_nat 8 31));
      v_14795 <- eval (rorHelper v_14790 (uvalueMInt v_14793) 0);
      store v_14789 v_14795 1;
      v_14797 <- eval (eq v_14793 (expression.bv_nat 8 0));
      v_14798 <- eval (notBool_ v_14797);
      v_14800 <- eval (eq (extract v_14795 0 1) (expression.bv_nat 1 1));
      v_14802 <- getRegister cf;
      v_14807 <- eval (eq v_14793 (expression.bv_nat 8 1));
      v_14815 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14807 (notBool_ (eq v_14800 (eq (extract v_14795 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14807) (bit_or (bit_and v_14798 undef) (bit_and v_14797 (eq v_14815 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14798 v_14800) (bit_and v_14797 (eq v_14802 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2658 : imm int) (v_2659 : Mem) => do
      v_14824 <- evaluateAddress v_2659;
      v_14825 <- load v_14824 1;
      v_14827 <- eval (bv_and (handleImmediateWithSignExtend v_2658 8 8) (expression.bv_nat 8 31));
      v_14829 <- eval (rorHelper v_14825 (uvalueMInt v_14827) 0);
      store v_14824 v_14829 1;
      v_14831 <- eval (eq v_14827 (expression.bv_nat 8 0));
      v_14832 <- eval (notBool_ v_14831);
      v_14834 <- eval (eq (extract v_14829 0 1) (expression.bv_nat 1 1));
      v_14836 <- getRegister cf;
      v_14841 <- eval (eq v_14827 (expression.bv_nat 8 1));
      v_14849 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14841 (notBool_ (eq v_14834 (eq (extract v_14829 1 2) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_14841) (bit_or (bit_and v_14832 undef) (bit_and v_14831 (eq v_14849 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14832 v_14834) (bit_and v_14831 (eq v_14836 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

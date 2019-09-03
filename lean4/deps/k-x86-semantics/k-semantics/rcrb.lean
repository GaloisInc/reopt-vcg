def rcrb1 : instruction :=
  definst "rcrb" $ do
    pattern fun cl (v_2455 : reg (bv 8)) => do
      v_4234 <- getRegister cf;
      v_4237 <- getRegister v_2455;
      v_4239 <- getRegister rcx;
      v_4243 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_4239 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_4245 <- eval (rorHelper (concat (mux (eq v_4234 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4237) (uvalueMInt v_4243) 0);
      v_4247 <- eval (extract v_4243 1 9);
      v_4248 <- eval (eq v_4247 (expression.bv_nat 8 1));
      v_4257 <- eval (eq v_4247 (expression.bv_nat 8 0));
      v_4260 <- getRegister of;
      setRegister (lhs.of_reg v_2455) (extract v_4245 1 9);
      setRegister of (mux (bit_or (bit_and v_4248 (notBool_ (eq (eq (extract v_4245 1 2) (expression.bv_nat 1 1)) (eq (extract v_4245 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4248) (bit_or (bit_and (notBool_ v_4257) undef) (bit_and v_4257 (eq v_4260 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4245 0 1);
      pure ()
    pat_end;
    pattern fun (v_2456 : imm int) (v_2460 : reg (bv 8)) => do
      v_4271 <- getRegister cf;
      v_4274 <- getRegister v_2460;
      v_4279 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_2456 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_4281 <- eval (rorHelper (concat (mux (eq v_4271 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4274) (uvalueMInt v_4279) 0);
      v_4283 <- eval (extract v_4279 1 9);
      v_4284 <- eval (eq v_4283 (expression.bv_nat 8 1));
      v_4293 <- eval (eq v_4283 (expression.bv_nat 8 0));
      v_4296 <- getRegister of;
      setRegister (lhs.of_reg v_2460) (extract v_4281 1 9);
      setRegister of (mux (bit_or (bit_and v_4284 (notBool_ (eq (eq (extract v_4281 1 2) (expression.bv_nat 1 1)) (eq (extract v_4281 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_4284) (bit_or (bit_and (notBool_ v_4293) undef) (bit_and v_4293 (eq v_4296 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4281 0 1);
      pure ()
    pat_end;
    pattern fun $0x1 (v_2464 : reg (bv 8)) => do
      v_4307 <- getRegister cf;
      v_4310 <- getRegister v_2464;
      v_4311 <- eval (concat (mux (eq v_4307 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4310);
      v_4313 <- eval (bitwidthMInt v_4311);
      v_4314 <- eval (sub v_4313 1);
      v_4318 <- eval (add (lshr v_4311 1) (concat (extract v_4311 v_4314 v_4313) (mi v_4314 0)));
      setRegister (lhs.of_reg v_2464) (extract v_4318 1 9);
      setRegister of (mux (notBool_ (eq (eq (extract v_4318 1 2) (expression.bv_nat 1 1)) (eq (extract v_4318 2 3) (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_4318 0 1);
      pure ()
    pat_end;
    pattern fun cl (v_2442 : Mem) => do
      v_13677 <- evaluateAddress v_2442;
      v_13678 <- getRegister cf;
      v_13681 <- load v_13677 1;
      v_13683 <- getRegister rcx;
      v_13687 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (extract v_13683 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_13689 <- eval (rorHelper (concat (mux (eq v_13678 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13681) (uvalueMInt v_13687) 0);
      store v_13677 (extract v_13689 1 9) 1;
      v_13693 <- eval (extract v_13687 1 9);
      v_13694 <- eval (eq v_13693 (expression.bv_nat 8 1));
      v_13703 <- eval (eq v_13693 (expression.bv_nat 8 0));
      v_13706 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13694 (notBool_ (eq (eq (extract v_13689 1 2) (expression.bv_nat 1 1)) (eq (extract v_13689 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13694) (bit_or (bit_and (notBool_ v_13703) undef) (bit_and v_13703 (eq v_13706 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13689 0 1);
      pure ()
    pat_end;
    pattern fun (v_2445 : imm int) (v_2446 : Mem) => do
      v_13715 <- evaluateAddress v_2446;
      v_13716 <- getRegister cf;
      v_13719 <- load v_13715 1;
      v_13724 <- eval (urem (concat (expression.bv_nat 1 0) (bv_and (handleImmediateWithSignExtend v_2445 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 9 9));
      v_13726 <- eval (rorHelper (concat (mux (eq v_13716 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_13719) (uvalueMInt v_13724) 0);
      store v_13715 (extract v_13726 1 9) 1;
      v_13730 <- eval (extract v_13724 1 9);
      v_13731 <- eval (eq v_13730 (expression.bv_nat 8 1));
      v_13740 <- eval (eq v_13730 (expression.bv_nat 8 0));
      v_13743 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_13731 (notBool_ (eq (eq (extract v_13726 1 2) (expression.bv_nat 1 1)) (eq (extract v_13726 2 3) (expression.bv_nat 1 1))))) (bit_and (notBool_ v_13731) (bit_or (bit_and (notBool_ v_13740) undef) (bit_and v_13740 (eq v_13743 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (extract v_13726 0 1);
      pure ()
    pat_end

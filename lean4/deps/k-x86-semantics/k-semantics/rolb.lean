def rolb1 : instruction :=
  definst "rolb" $ do
    pattern fun cl (v_2560 : reg (bv 8)) => do
      v_4759 <- getRegister rcx;
      v_4761 <- eval (bv_and (extract v_4759 56 64) (expression.bv_nat 8 31));
      v_4762 <- eval (eq v_4761 (expression.bv_nat 8 0));
      v_4763 <- eval (notBool_ v_4762);
      v_4764 <- getRegister v_2560;
      v_4766 <- eval (rolHelper v_4764 (uvalueMInt v_4761) 0);
      v_4768 <- eval (eq (extract v_4766 7 8) (expression.bv_nat 1 1));
      v_4770 <- getRegister cf;
      v_4775 <- eval (eq v_4761 (expression.bv_nat 8 1));
      v_4783 <- getRegister of;
      setRegister (lhs.of_reg v_2560) v_4766;
      setRegister of (mux (bit_or (bit_and v_4775 (notBool_ (eq (eq (extract v_4766 0 1) (expression.bv_nat 1 1)) v_4768))) (bit_and (notBool_ v_4775) (bit_or (bit_and v_4763 undef) (bit_and v_4762 (eq v_4783 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_4763 v_4768) (bit_and v_4762 (eq v_4770 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2561 : imm int) (v_2565 : reg (bv 8)) => do
      v_4794 <- eval (bv_and (handleImmediateWithSignExtend v_2561 8 8) (expression.bv_nat 8 31));
      v_4795 <- eval (eq v_4794 (expression.bv_nat 8 0));
      v_4796 <- eval (notBool_ v_4795);
      v_4797 <- getRegister v_2565;
      v_4799 <- eval (rolHelper v_4797 (uvalueMInt v_4794) 0);
      v_4801 <- eval (eq (extract v_4799 7 8) (expression.bv_nat 1 1));
      v_4803 <- getRegister cf;
      v_4808 <- eval (eq v_4794 (expression.bv_nat 8 1));
      v_4816 <- getRegister of;
      setRegister (lhs.of_reg v_2565) v_4799;
      setRegister of (mux (bit_or (bit_and v_4808 (notBool_ (eq (eq (extract v_4799 0 1) (expression.bv_nat 1 1)) v_4801))) (bit_and (notBool_ v_4808) (bit_or (bit_and v_4796 undef) (bit_and v_4795 (eq v_4816 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_4796 v_4801) (bit_and v_4795 (eq v_4803 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun $0x1 (v_2569 : reg (bv 8)) => do
      v_4826 <- getRegister v_2569;
      v_4828 <- eval (bitwidthMInt v_4826);
      v_4834 <- eval (add (extract (shl v_4826 1) 0 v_4828) (concat (mi (sub v_4828 1) 0) (extract v_4826 0 1)));
      v_4835 <- eval (extract v_4834 7 8);
      setRegister (lhs.of_reg v_2569) v_4834;
      setRegister of (mux (notBool_ (eq (eq (extract v_4834 0 1) (expression.bv_nat 1 1)) (eq v_4835 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf v_4835;
      pure ()
    pat_end;
    pattern fun cl (v_2547 : Mem) => do
      v_14177 <- evaluateAddress v_2547;
      v_14178 <- load v_14177 1;
      v_14179 <- getRegister rcx;
      v_14181 <- eval (bv_and (extract v_14179 56 64) (expression.bv_nat 8 31));
      v_14183 <- eval (rolHelper v_14178 (uvalueMInt v_14181) 0);
      store v_14177 v_14183 1;
      v_14185 <- eval (eq v_14181 (expression.bv_nat 8 0));
      v_14186 <- eval (notBool_ v_14185);
      v_14188 <- eval (eq (extract v_14183 7 8) (expression.bv_nat 1 1));
      v_14190 <- getRegister cf;
      v_14195 <- eval (eq v_14181 (expression.bv_nat 8 1));
      v_14203 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14195 (notBool_ (eq (eq (extract v_14183 0 1) (expression.bv_nat 1 1)) v_14188))) (bit_and (notBool_ v_14195) (bit_or (bit_and v_14186 undef) (bit_and v_14185 (eq v_14203 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14186 v_14188) (bit_and v_14185 (eq v_14190 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2550 : imm int) (v_2551 : Mem) => do
      v_14212 <- evaluateAddress v_2551;
      v_14213 <- load v_14212 1;
      v_14215 <- eval (bv_and (handleImmediateWithSignExtend v_2550 8 8) (expression.bv_nat 8 31));
      v_14217 <- eval (rolHelper v_14213 (uvalueMInt v_14215) 0);
      store v_14212 v_14217 1;
      v_14219 <- eval (eq v_14215 (expression.bv_nat 8 0));
      v_14220 <- eval (notBool_ v_14219);
      v_14222 <- eval (eq (extract v_14217 7 8) (expression.bv_nat 1 1));
      v_14224 <- getRegister cf;
      v_14229 <- eval (eq v_14215 (expression.bv_nat 8 1));
      v_14237 <- getRegister of;
      setRegister of (mux (bit_or (bit_and v_14229 (notBool_ (eq (eq (extract v_14217 0 1) (expression.bv_nat 1 1)) v_14222))) (bit_and (notBool_ v_14229) (bit_or (bit_and v_14220 undef) (bit_and v_14219 (eq v_14237 (expression.bv_nat 1 1)))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister cf (mux (bit_or (bit_and v_14220 v_14222) (bit_and v_14219 (eq v_14224 (expression.bv_nat 1 1)))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end

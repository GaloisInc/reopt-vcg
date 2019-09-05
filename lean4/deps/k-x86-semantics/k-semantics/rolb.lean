def rolb1 : instruction :=
  definst "rolb" $ do
    pattern fun cl (v_2637 : reg (bv 8)) => do
      v_4768 <- getRegister rcx;
      v_4770 <- eval (bv_and (extract v_4768 56 64) (expression.bv_nat 8 31));
      v_4771 <- eval (eq v_4770 (expression.bv_nat 8 1));
      v_4772 <- getRegister v_2637;
      v_4773 <- eval (rol v_4772 v_4770);
      v_4775 <- eval (isBitSet v_4773 7);
      v_4780 <- eval (eq v_4770 (expression.bv_nat 8 0));
      v_4781 <- eval (notBool_ v_4780);
      v_4783 <- getRegister of;
      v_4790 <- getRegister cf;
      setRegister (lhs.of_reg v_2637) v_4773;
      setRegister cf (bit_or (bit_and v_4781 v_4775) (bit_and v_4780 (eq v_4790 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_4771 (notBool_ (eq (isBitSet v_4773 0) v_4775))) (bit_and (notBool_ v_4771) (bit_or (bit_and v_4781 undef) (bit_and v_4780 (eq v_4783 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2640 : imm int) (v_2642 : reg (bv 8)) => do
      v_4798 <- eval (bv_and (handleImmediateWithSignExtend v_2640 8 8) (expression.bv_nat 8 31));
      v_4799 <- eval (eq v_4798 (expression.bv_nat 8 1));
      v_4800 <- getRegister v_2642;
      v_4801 <- eval (rol v_4800 v_4798);
      v_4803 <- eval (isBitSet v_4801 7);
      v_4808 <- eval (eq v_4798 (expression.bv_nat 8 0));
      v_4809 <- eval (notBool_ v_4808);
      v_4811 <- getRegister of;
      v_4818 <- getRegister cf;
      setRegister (lhs.of_reg v_2642) v_4801;
      setRegister cf (bit_or (bit_and v_4809 v_4803) (bit_and v_4808 (eq v_4818 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_4799 (notBool_ (eq (isBitSet v_4801 0) v_4803))) (bit_and (notBool_ v_4799) (bit_or (bit_and v_4809 undef) (bit_and v_4808 (eq v_4811 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2613 : Mem) => do
      v_12212 <- evaluateAddress v_2613;
      v_12213 <- load v_12212 1;
      v_12214 <- getRegister rcx;
      v_12216 <- eval (bv_and (extract v_12214 56 64) (expression.bv_nat 8 31));
      v_12217 <- eval (rol v_12213 v_12216);
      store v_12212 v_12217 1;
      v_12219 <- eval (eq v_12216 (expression.bv_nat 8 1));
      v_12221 <- eval (isBitSet v_12217 7);
      v_12226 <- eval (eq v_12216 (expression.bv_nat 8 0));
      v_12227 <- eval (notBool_ v_12226);
      v_12229 <- getRegister of;
      v_12236 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12227 v_12221) (bit_and v_12226 (eq v_12236 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12219 (notBool_ (eq (isBitSet v_12217 0) v_12221))) (bit_and (notBool_ v_12219) (bit_or (bit_and v_12227 undef) (bit_and v_12226 (eq v_12229 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2616 : imm int) (v_2617 : Mem) => do
      v_12242 <- evaluateAddress v_2617;
      v_12243 <- load v_12242 1;
      v_12245 <- eval (bv_and (handleImmediateWithSignExtend v_2616 8 8) (expression.bv_nat 8 31));
      v_12246 <- eval (rol v_12243 v_12245);
      store v_12242 v_12246 1;
      v_12248 <- eval (eq v_12245 (expression.bv_nat 8 1));
      v_12250 <- eval (isBitSet v_12246 7);
      v_12255 <- eval (eq v_12245 (expression.bv_nat 8 0));
      v_12256 <- eval (notBool_ v_12255);
      v_12258 <- getRegister of;
      v_12265 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12256 v_12250) (bit_and v_12255 (eq v_12265 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12248 (notBool_ (eq (isBitSet v_12246 0) v_12250))) (bit_and (notBool_ v_12248) (bit_or (bit_and v_12256 undef) (bit_and v_12255 (eq v_12258 (expression.bv_nat 1 1))))));
      pure ()
    pat_end

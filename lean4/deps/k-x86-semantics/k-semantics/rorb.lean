def rorb1 : instruction :=
  definst "rorb" $ do
    pattern fun cl (v_2745 : reg (bv 8)) => do
      v_5152 <- getRegister rcx;
      v_5154 <- eval (bv_and (extract v_5152 56 64) (expression.bv_nat 8 31));
      v_5155 <- eval (eq v_5154 (expression.bv_nat 8 1));
      v_5156 <- getRegister v_2745;
      v_5157 <- eval (ror v_5156 v_5154);
      v_5158 <- eval (isBitSet v_5157 0);
      v_5164 <- eval (eq v_5154 (expression.bv_nat 8 0));
      v_5165 <- eval (notBool_ v_5164);
      v_5167 <- getRegister of;
      v_5174 <- getRegister cf;
      setRegister (lhs.of_reg v_2745) v_5157;
      setRegister cf (bit_or (bit_and v_5165 v_5158) (bit_and v_5164 (eq v_5174 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5155 (notBool_ (eq v_5158 (isBitSet v_5157 1)))) (bit_and (notBool_ v_5155) (bit_or (bit_and v_5165 undef) (bit_and v_5164 (eq v_5167 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2748 : imm int) (v_2750 : reg (bv 8)) => do
      v_5182 <- eval (bv_and (handleImmediateWithSignExtend v_2748 8 8) (expression.bv_nat 8 31));
      v_5183 <- eval (eq v_5182 (expression.bv_nat 8 1));
      v_5184 <- getRegister v_2750;
      v_5185 <- eval (ror v_5184 v_5182);
      v_5186 <- eval (isBitSet v_5185 0);
      v_5192 <- eval (eq v_5182 (expression.bv_nat 8 0));
      v_5193 <- eval (notBool_ v_5192);
      v_5195 <- getRegister of;
      v_5202 <- getRegister cf;
      setRegister (lhs.of_reg v_2750) v_5185;
      setRegister cf (bit_or (bit_and v_5193 v_5186) (bit_and v_5192 (eq v_5202 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5183 (notBool_ (eq v_5186 (isBitSet v_5185 1)))) (bit_and (notBool_ v_5183) (bit_or (bit_and v_5193 undef) (bit_and v_5192 (eq v_5195 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2721 : Mem) => do
      v_12535 <- evaluateAddress v_2721;
      v_12536 <- load v_12535 1;
      v_12537 <- getRegister rcx;
      v_12539 <- eval (bv_and (extract v_12537 56 64) (expression.bv_nat 8 31));
      v_12540 <- eval (ror v_12536 v_12539);
      store v_12535 v_12540 1;
      v_12542 <- eval (eq v_12539 (expression.bv_nat 8 1));
      v_12543 <- eval (isBitSet v_12540 0);
      v_12549 <- eval (eq v_12539 (expression.bv_nat 8 0));
      v_12550 <- eval (notBool_ v_12549);
      v_12552 <- getRegister of;
      v_12559 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12550 v_12543) (bit_and v_12549 (eq v_12559 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12542 (notBool_ (eq v_12543 (isBitSet v_12540 1)))) (bit_and (notBool_ v_12542) (bit_or (bit_and v_12550 undef) (bit_and v_12549 (eq v_12552 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2724 : imm int) (v_2725 : Mem) => do
      v_12565 <- evaluateAddress v_2725;
      v_12566 <- load v_12565 1;
      v_12568 <- eval (bv_and (handleImmediateWithSignExtend v_2724 8 8) (expression.bv_nat 8 31));
      v_12569 <- eval (ror v_12566 v_12568);
      store v_12565 v_12569 1;
      v_12571 <- eval (eq v_12568 (expression.bv_nat 8 1));
      v_12572 <- eval (isBitSet v_12569 0);
      v_12578 <- eval (eq v_12568 (expression.bv_nat 8 0));
      v_12579 <- eval (notBool_ v_12578);
      v_12581 <- getRegister of;
      v_12588 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12579 v_12572) (bit_and v_12578 (eq v_12588 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12571 (notBool_ (eq v_12572 (isBitSet v_12569 1)))) (bit_and (notBool_ v_12571) (bit_or (bit_and v_12579 undef) (bit_and v_12578 (eq v_12581 (expression.bv_nat 1 1))))));
      pure ()
    pat_end

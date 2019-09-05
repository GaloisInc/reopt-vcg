def rorl1 : instruction :=
  definst "rorl" $ do
    pattern fun cl (v_2768 : reg (bv 32)) => do
      v_5228 <- getRegister rcx;
      v_5230 <- eval (bv_and (extract v_5228 56 64) (expression.bv_nat 8 31));
      v_5231 <- eval (eq v_5230 (expression.bv_nat 8 1));
      v_5232 <- getRegister v_2768;
      v_5234 <- eval (ror v_5232 (concat (expression.bv_nat 24 0) v_5230));
      v_5235 <- eval (isBitSet v_5234 0);
      v_5241 <- eval (eq v_5230 (expression.bv_nat 8 0));
      v_5242 <- eval (notBool_ v_5241);
      v_5244 <- getRegister of;
      v_5251 <- getRegister cf;
      setRegister (lhs.of_reg v_2768) v_5234;
      setRegister cf (bit_or (bit_and v_5242 v_5235) (bit_and v_5241 (eq v_5251 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5231 (notBool_ (eq v_5235 (isBitSet v_5234 1)))) (bit_and (notBool_ v_5231) (bit_or (bit_and v_5242 undef) (bit_and v_5241 (eq v_5244 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2771 : imm int) (v_2773 : reg (bv 32)) => do
      v_5259 <- eval (bv_and (handleImmediateWithSignExtend v_2771 8 8) (expression.bv_nat 8 31));
      v_5260 <- eval (eq v_5259 (expression.bv_nat 8 1));
      v_5261 <- getRegister v_2773;
      v_5263 <- eval (ror v_5261 (concat (expression.bv_nat 24 0) v_5259));
      v_5264 <- eval (isBitSet v_5263 0);
      v_5270 <- eval (eq v_5259 (expression.bv_nat 8 0));
      v_5271 <- eval (notBool_ v_5270);
      v_5273 <- getRegister of;
      v_5280 <- getRegister cf;
      setRegister (lhs.of_reg v_2773) v_5263;
      setRegister cf (bit_or (bit_and v_5271 v_5264) (bit_and v_5270 (eq v_5280 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_5260 (notBool_ (eq v_5264 (isBitSet v_5263 1)))) (bit_and (notBool_ v_5260) (bit_or (bit_and v_5271 undef) (bit_and v_5270 (eq v_5273 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2757 : Mem) => do
      v_12614 <- evaluateAddress v_2757;
      v_12615 <- load v_12614 4;
      v_12616 <- getRegister rcx;
      v_12618 <- eval (bv_and (extract v_12616 56 64) (expression.bv_nat 8 31));
      v_12620 <- eval (ror v_12615 (concat (expression.bv_nat 24 0) v_12618));
      store v_12614 v_12620 4;
      v_12622 <- eval (eq v_12618 (expression.bv_nat 8 1));
      v_12623 <- eval (isBitSet v_12620 0);
      v_12629 <- eval (eq v_12618 (expression.bv_nat 8 0));
      v_12630 <- eval (notBool_ v_12629);
      v_12632 <- getRegister of;
      v_12639 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12630 v_12623) (bit_and v_12629 (eq v_12639 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12622 (notBool_ (eq v_12623 (isBitSet v_12620 1)))) (bit_and (notBool_ v_12622) (bit_or (bit_and v_12630 undef) (bit_and v_12629 (eq v_12632 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2760 : imm int) (v_2761 : Mem) => do
      v_12645 <- evaluateAddress v_2761;
      v_12646 <- load v_12645 4;
      v_12648 <- eval (bv_and (handleImmediateWithSignExtend v_2760 8 8) (expression.bv_nat 8 31));
      v_12650 <- eval (ror v_12646 (concat (expression.bv_nat 24 0) v_12648));
      store v_12645 v_12650 4;
      v_12652 <- eval (eq v_12648 (expression.bv_nat 8 1));
      v_12653 <- eval (isBitSet v_12650 0);
      v_12659 <- eval (eq v_12648 (expression.bv_nat 8 0));
      v_12660 <- eval (notBool_ v_12659);
      v_12662 <- getRegister of;
      v_12669 <- getRegister cf;
      setRegister cf (bit_or (bit_and v_12660 v_12653) (bit_and v_12659 (eq v_12669 (expression.bv_nat 1 1))));
      setRegister of (bit_or (bit_and v_12652 (notBool_ (eq v_12653 (isBitSet v_12650 1)))) (bit_and (notBool_ v_12652) (bit_or (bit_and v_12660 undef) (bit_and v_12659 (eq v_12662 (expression.bv_nat 1 1))))));
      pure ()
    pat_end

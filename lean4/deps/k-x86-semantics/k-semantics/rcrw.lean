def rcrw1 : instruction :=
  definst "rcrw" $ do
    pattern fun cl (v_2598 : reg (bv 16)) => do
      v_4612 <- getRegister rcx;
      v_4616 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_4612 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4617 <- eval (extract v_4616 9 17);
      v_4618 <- eval (eq v_4617 (expression.bv_nat 8 1));
      v_4619 <- getRegister cf;
      v_4622 <- getRegister v_2598;
      v_4624 <- eval (ror (concat (mux (eq v_4619 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4622) v_4616);
      v_4631 <- eval (eq v_4617 (expression.bv_nat 8 0));
      v_4634 <- getRegister of;
      setRegister (lhs.of_reg v_2598) (extract v_4624 1 17);
      setRegister cf (isBitSet v_4624 0);
      setRegister of (bit_or (bit_and v_4618 (notBool_ (eq (isBitSet v_4624 1) (isBitSet v_4624 2)))) (bit_and (notBool_ v_4618) (bit_or (bit_and (notBool_ v_4631) undef) (bit_and v_4631 (eq v_4634 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2605 : imm int) (v_2602 : reg (bv 16)) => do
      v_4648 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2605 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_4649 <- eval (extract v_4648 9 17);
      v_4650 <- eval (eq v_4649 (expression.bv_nat 8 1));
      v_4651 <- getRegister cf;
      v_4654 <- getRegister v_2602;
      v_4656 <- eval (ror (concat (mux (eq v_4651 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_4654) v_4648);
      v_4663 <- eval (eq v_4649 (expression.bv_nat 8 0));
      v_4666 <- getRegister of;
      setRegister (lhs.of_reg v_2602) (extract v_4656 1 17);
      setRegister cf (isBitSet v_4656 0);
      setRegister of (bit_or (bit_and v_4650 (notBool_ (eq (isBitSet v_4656 1) (isBitSet v_4656 2)))) (bit_and (notBool_ v_4650) (bit_or (bit_and (notBool_ v_4663) undef) (bit_and v_4663 (eq v_4666 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun cl (v_2590 : Mem) => do
      v_12113 <- evaluateAddress v_2590;
      v_12114 <- getRegister cf;
      v_12117 <- load v_12113 2;
      v_12119 <- getRegister rcx;
      v_12123 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (extract v_12119 56 64) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_12124 <- eval (ror (concat (mux (eq v_12114 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_12117) v_12123);
      store v_12113 (extract v_12124 1 17) 2;
      v_12127 <- eval (extract v_12123 9 17);
      v_12128 <- eval (eq v_12127 (expression.bv_nat 8 1));
      v_12135 <- eval (eq v_12127 (expression.bv_nat 8 0));
      v_12138 <- getRegister of;
      setRegister cf (isBitSet v_12124 0);
      setRegister of (bit_or (bit_and v_12128 (notBool_ (eq (isBitSet v_12124 1) (isBitSet v_12124 2)))) (bit_and (notBool_ v_12128) (bit_or (bit_and (notBool_ v_12135) undef) (bit_and v_12135 (eq v_12138 (expression.bv_nat 1 1))))));
      pure ()
    pat_end;
    pattern fun (v_2593 : imm int) (v_2594 : Mem) => do
      v_12147 <- evaluateAddress v_2594;
      v_12148 <- getRegister cf;
      v_12151 <- load v_12147 2;
      v_12156 <- eval (urem (concat (expression.bv_nat 9 0) (bv_and (handleImmediateWithSignExtend v_2593 8 8) (expression.bv_nat 8 31))) (expression.bv_nat 17 17));
      v_12157 <- eval (ror (concat (mux (eq v_12148 (expression.bv_nat 1 1)) (expression.bv_nat 1 1) (expression.bv_nat 1 0)) v_12151) v_12156);
      store v_12147 (extract v_12157 1 17) 2;
      v_12160 <- eval (extract v_12156 9 17);
      v_12161 <- eval (eq v_12160 (expression.bv_nat 8 1));
      v_12168 <- eval (eq v_12160 (expression.bv_nat 8 0));
      v_12171 <- getRegister of;
      setRegister cf (isBitSet v_12157 0);
      setRegister of (bit_or (bit_and v_12161 (notBool_ (eq (isBitSet v_12157 1) (isBitSet v_12157 2)))) (bit_and (notBool_ v_12161) (bit_or (bit_and (notBool_ v_12168) undef) (bit_and v_12168 (eq v_12171 (expression.bv_nat 1 1))))));
      pure ()
    pat_end
